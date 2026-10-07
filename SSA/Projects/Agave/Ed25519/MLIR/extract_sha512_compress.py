#!/usr/bin/env python3
"""Extract the pinned SHA-512 dispatcher and AVX2 backend without rewriting them.

The original Ed25519 artifact references this separately compiled dependency.
Compile only the locked sha2 package, with its original empty feature set and
release profile. Both runtime paths remain present; no forced soft/AVX2 cfg is
used. The soft 80-round body is inlined in the dispatcher by rustc itself.
"""
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tomllib

if not __debug__:
    raise RuntimeError("Artifact validation requires Python assertions enabled")

HERE = Path(__file__).resolve().parent
SOURCES = HERE / "source-sha2"
MANIFEST = HERE / "sha2-source-manifest.json"
TARGETS = {
    "agave_sha512_compress_dispatch": "4sha26sha51211compress512",
    "agave_sha512_compress_avx2": "4sha26sha5128x86_avx28compress",
}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def check_sources():
    source = json.loads(MANIFEST.read_text())
    packages = tomllib.loads((HERE / "Cargo.extract.lock").read_text())["package"]
    package, = [p for p in packages if p["name"] == "sha2"]
    assert source["crate"] == "sha2"
    assert package["version"] == source["version"] == "0.11.0"
    assert source["dependency_features"] == source["rustflags"] == []
    files = source["files_sha256"]
    actual = {str(p.relative_to(SOURCES)) for p in SOURCES.rglob("*") if p.is_file()}
    assert len(files) == 49 and set(files) == actual, "incomplete source inventory"
    assert package["checksum"] == source["registry_package_sha256"]
    for rel, expected in source["files_sha256"].items():
        assert sha(SOURCES / rel) == expected, rel
    return source


def definitions(text):
    return {m[1]: m[0] for m in re.finditer(
        r"^define [^\n]*?@([^\s(]+)\([^\n]*\).*?^}", text, re.M | re.S)}


def caller_symbol():
    caller = (HERE / "generated/agave_scalar_from_sha512.ll").read_text()
    symbols = set(re.findall(r"@([^\s(]+4sha26sha51211compress512)\(", caller))
    assert len(symbols) == 1, symbols
    return symbols.pop()


def check_artifacts(out):
    """Check a complete, self-contained inventory, not just listed file hashes."""
    check_sources()
    manifest = json.loads((out / "sha512-compress-manifest.json").read_text())
    assert manifest["source_manifest_sha256"] == sha(MANIFEST)
    assert manifest["extract_script_sha256"] == sha(__file__)
    assert manifest["lock_sha256"] == sha(HERE / "Cargo.extract.lock")
    assert manifest["base_manifest_sha256"] == sha(HERE / "generated/manifest.json")
    assert manifest["caller_artifact_sha256"] == sha(HERE / "generated/agave_scalar_from_sha512.ll")
    assert manifest["dependency_features"] == manifest["dependency_rustflags"] == []
    assert manifest["caller_external_symbol"] == caller_symbol()
    assert manifest["tools"]["rustc"] == json.loads((HERE / "generated/manifest.json").read_text())["rustc"]
    assert set(manifest["tools"]) == {"rustc", "llvm-extract", "opt", "mlir-translate"}
    for tool in ("llvm-extract", "opt", "mlir-translate"):
        assert "LLVM version 22." in manifest["tools"][tool]
    assert set(manifest["kernels"]) == set(TARGETS), "incomplete kernel inventory"
    for kernel, entry in manifest["kernels"].items():
        symbol = entry["target_symbol"]
        assert symbol.endswith(TARGETS[kernel])
        if kernel == "agave_sha512_compress_dispatch":
            assert symbol == caller_symbol()
        assert entry["llvm_inlining_applied_after_rustc"] is False
        assert set(entry["files_sha256"]) == {
            f"{kernel}.ll", f"{kernel}.mlir", f"{kernel}.original.ll"}
        for rel, expected in entry["files_sha256"].items():
            assert sha(out / rel) == expected, rel
        original = (out / f"{kernel}.original.ll").read_text()
        assert set(definitions(original)) == {symbol}, "wrong original function"
        assert original == definitions(original)[symbol] + "\n"
        assert hashlib.sha256(original.rstrip("\n").encode()).hexdigest() == entry["original_definition_sha256"]
        assert set(definitions((out / f"{kernel}.ll").read_text())) == {symbol}
        text = (out / f"{kernel}.mlir").read_text()
        assert dict(Counter(re.findall(r'"(llvm\.[^"]+)"\(', text))) == entry["mlir_operations"]
        globals_ = set(re.findall(r"global_name = @([^, >}]+)", text))
        assert globals_ == set(entry["original_global_definitions"]), "incomplete global inventory"
        for name, value in entry["original_global_definitions"].items():
            definition = value["definition"]
            assert definition.startswith(f"@{name} = ") and "\n" not in definition
            assert hashlib.sha256(definition.encode()).hexdigest() == value["sha256"]
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", type=Path,
                        help="original pinned Ed25519 extraction build directory")
    parser.add_argument("--llvm-bin", type=Path)
    parser.add_argument("--llvm-lib", type=Path)
    parser.add_argument("--out", type=Path, default=HERE / "generated")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--sources-only", action="store_true")
    args = parser.parse_args()
    source = check_sources()
    if args.sources_only:
        print(f"Validated {len(source['files_sha256'])} pinned sha2 source files")
        return
    out = args.out.resolve()
    manifest_path = out / "sha512-compress-manifest.json"
    base_manifest = HERE / "generated/manifest.json"
    caller_artifact = HERE / "generated/agave_scalar_from_sha512.ll"
    if args.check:
        manifest = check_artifacts(out)
        print(f"Validated {len(manifest['kernels'])} exact SHA-512 compression artifacts")
        return
    if not (args.build and args.llvm_bin):
        parser.error("--build and --llvm-bin required for extraction")
    build = args.build.resolve()
    assert sha(build / "Cargo.lock") == sha(HERE / "Cargo.extract.lock")
    assert sha(build / "Cargo.toml") == sha(HERE / "Cargo.extract.toml")
    dep_infos = list((build / "target/release/deps").glob("sha2-*.d"))
    roots = set()
    for dep in dep_infos:
        roots.update(re.findall(r"([^\s:]+/sha2-0\.11\.0)/src/lib\.rs", dep.read_text()))
    assert len(roots) == 1, roots
    compiled_source = Path(roots.pop())
    for rel, expected in source["files_sha256"].items():
        assert sha(compiled_source / rel) == expected, f"compiler input differs: {rel}"
    expected_dispatcher = caller_symbol()
    env = os.environ.copy()
    # Reject rather than silently reinterpret a caller's alternate backend.
    assert not env.get("RUSTFLAGS") and not env.get("CARGO_ENCODED_RUSTFLAGS")
    if args.llvm_lib:
        env["LD_LIBRARY_PATH"] = str(args.llvm_lib.resolve())
    command = ["cargo", "+1.98.1", "rustc", "--manifest-path", str(build / "Cargo.toml"),
               "--offline", "--locked", "--release", "--lib", "-p", "sha2",
               "--", "--emit=llvm-ir"]
    subprocess.run(command, check=True, env=env, cwd=build)
    candidates = sorted((build / "target/release/deps").glob("sha2-*.ll"))
    candidates = [p for p in candidates if all(s in p.read_text() for s in TARGETS.values())]
    assert len(candidates) == 1, candidates
    crate_ir, = candidates
    fingerprint_path = crate_ir.parent.parent / ".fingerprint" / crate_ir.stem / "lib-sha2.json"
    fingerprint = json.loads(fingerprint_path.read_text())
    assert json.loads(fingerprint["features"]) == [], "sha2 features changed"
    assert fingerprint["rustflags"] == [], "sha2 compiler flags changed"
    original = crate_ir.read_text()
    original_definitions = definitions(original)
    global_definitions = {m[1]: m[0] for m in re.finditer(
        r"^@([^\s=]+) = [^\n]+$", original, re.M)}
    versions = {"rustc": subprocess.check_output(
        ["rustc", "+1.98.1", "-vV"], text=True, env=env)}
    assert versions["rustc"] == json.loads(base_manifest.read_text())["rustc"]
    for tool in ("llvm-extract", "opt", "mlir-translate"):
        versions[tool] = subprocess.check_output(
            [str(args.llvm_bin / tool), "--version"], text=True, env=env)
        assert "LLVM version 22." in versions[tool]
    out.mkdir(parents=True, exist_ok=True)
    commands, kernels = [command], {}
    for name, suffix in TARGETS.items():
        target, = [s for s in original_definitions if s.endswith(suffix)]
        if name == "agave_sha512_compress_dispatch":
            assert target == expected_dispatcher, (target, expected_dispatcher)
        ll, mlir = out / f"{name}.ll", out / f"{name}.mlir"
        original_ll = out / f"{name}.original.ll"
        original_ll.write_text(original_definitions[target] + "\n")
        for command in (
            [args.llvm_bin / "llvm-extract", "--keep-const-init", f"--func={target}",
             "-S", crate_ir, "-o", ll],
            [args.llvm_bin / "opt", "-S", "--passes=internalize,globaldce",
             f"--internalize-public-api-list={target}", ll, "-o", ll],
            [args.llvm_bin / "mlir-translate", "--import-llvm", "--mlir-print-op-generic",
             ll, "-o", mlir],
        ):
            command = [str(x) for x in command]
            subprocess.run(command, check=True, env=env)
            commands.append(command)
        text = mlir.read_text()
        referenced_globals = list(dict.fromkeys(re.findall(r"global_name = @([^, >}]+)", text)))
        # Mutable cache initializers may become external declarations during
        # llvm-extract. Retain their ORIGINAL definition, without pretending
        # that successful region import initializes a global allocation.
        original_globals = {}
        for symbol in referenced_globals:
            assert symbol in global_definitions, f"missing original global: {symbol}"
            definition = global_definitions[symbol]
            original_globals[symbol] = {
                "definition": definition,
                "sha256": hashlib.sha256(definition.encode()).hexdigest(),
            }
        kernels[name] = {
            "target_symbol": target,
            "original_definition_sha256": hashlib.sha256(original_definitions[target].encode()).hexdigest(),
            "llvm_inlining_applied_after_rustc": False,
            "original_global_definitions": original_globals,
            "mlir_operations": dict(sorted(Counter(re.findall(r'"(llvm\.[^"]+)"\(', text)).items())),
            "files_sha256": {p.name: sha(p) for p in (ll, mlir, original_ll)},
        }
    manifest = {
        "source_manifest_sha256": sha(MANIFEST),
        "base_manifest_sha256": sha(base_manifest),
        "caller_artifact_sha256": sha(caller_artifact),
        "lock_sha256": sha(HERE / "Cargo.extract.lock"),
        "extract_script_sha256": sha(__file__),
        "crate_llvm_ir_sha256": sha(crate_ir),
        "crate_llvm_ir_path": str(crate_ir),
        "compiled_source_path": str(compiled_source),
        "cargo_working_directory": str(build),
        "dependency_features": json.loads(fingerprint["features"]),
        "dependency_rustflags": fingerprint["rustflags"],
        "caller_external_symbol": expected_dispatcher,
        "tools": versions, "commands": commands, "kernels": kernels,
        "boundary": "Original sha2 dependency, original runtime dispatch, no Rust wrappers or body rewrites. "
                    "Rust/LLVM compilation and MLIR import remain trusted. CPUID/cache effects and both "
                    "backend execution refinements are separate proof obligations.",
    }
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    check_artifacts(out)
    print(f"Extracted {len(kernels)} original SHA-512 compression regions")


if __name__ == "__main__":
    main()

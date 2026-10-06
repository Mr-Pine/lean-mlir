#!/usr/bin/env python3
"""Extract pinned Agave Ed25519 kernels without rewriting their Rust bodies.

The archived crate is copied, and observation wrappers are appended to the
owning modules. LLVM extraction and optimization are performed only by LLVM.
"""
import argparse
import collections
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
FEATURES = "alloc,precomputed-tables,zeroize,rand_core,digest"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_source():
    manifest = json.loads((HERE / "source-manifest.json").read_text())
    for name, expected in manifest["files_sha256"].items():
        assert sha(HERE / "source" / name) == expected, f"source changed: {name}"
    return manifest


def functions(text):
    return {m.group(1): m.group(0) for m in re.finditer(
        r"^define [^\n]*?@([^\s(]+)\([^\n]*\).*?^}", text, re.M | re.S)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--llvm-bin", type=Path, required=True)
    parser.add_argument("--llvm-lib", type=Path)
    parser.add_argument("--cargo", default="cargo")
    args = parser.parse_args()
    args.out = args.out.resolve()
    args.llvm_bin = args.llvm_bin.resolve()
    manifest = verify_source()
    args.out.mkdir(parents=True, exist_ok=True)
    build = args.out / "build"
    shutil.copytree(HERE / "source", build, dirs_exist_ok=True)
    shutil.copyfile(HERE / "Cargo.extract.toml", build / "Cargo.toml")
    shutil.copyfile(HERE / "Cargo.extract.lock", build / "Cargo.lock")
    wrapper_modules = {
        "wrappers.rs": "src/lib.rs",
        "reduce64_wrapper.rs": "src/backend/vector/avx2/field.rs",
        "point_wrappers.rs": "src/backend/vector/avx2/edwards.rs",
    }
    for wrapper, module in wrapper_modules.items():
        if (HERE / wrapper).exists():
            with (build / module).open("ab") as output:
                output.write((HERE / wrapper).read_bytes())
    env = os.environ.copy()
    if args.llvm_lib:
        env["LD_LIBRARY_PATH"] = str(args.llvm_lib.resolve())
    commands = []

    def run(command, log=None):
        command = [str(x) for x in command]
        commands.append(command)
        if log:
            with log.open("w") as output:
                subprocess.run(command, check=True, env=env, stdout=output, stderr=subprocess.STDOUT)
        else:
            subprocess.run(command, check=True, env=env)

    rust_version = subprocess.check_output(
        [args.cargo, "+1.98.1", "--version"], env=env, text=True)
    rustc_version = subprocess.check_output(
        ["rustup", "run", "1.98.1", "rustc", "-vV"], env=env, text=True)
    assert "release: 1.98.1\n" in rustc_version
    assert "LLVM version: 22.1.8\n" in rustc_version
    mlir_version = subprocess.check_output(
        [str(args.llvm_bin / "mlir-translate"), "--version"], env=env, text=True)
    assert "LLVM version 22." in mlir_version
    run([args.cargo, "+1.98.1", "rustc", "--manifest-path", build / "Cargo.toml",
         "--offline", "--locked", "--release", "--lib", "--no-default-features",
         "--features", FEATURES, "--", "--emit=llvm-ir"], args.out / "build.log")
    paths = list((build / "target/release/deps").glob("solana_ed25519*.ll"))
    assert len(paths) == 1, paths
    llvm_ir = paths[0]
    source_ir = llvm_ir.read_text()
    funcs = functions(source_ir)
    aliases = dict(re.findall(r"^@(agave_\w+) = [^\n]*?alias [^\n]*?ptr @([^\s]+)$", source_ir, re.M))
    names = sorted({name for name in funcs if name.startswith("agave_")} | aliases.keys())
    generated = args.out / "generated"
    generated.mkdir(exist_ok=True)
    inventory = {}
    for name in names:
        target = aliases.get(name, name)
        body = funcs[target]
        internal_calls = [c for c in re.findall(r"\bcall [^\n]*?@([^\s(]+)", body) if c in funcs]
        # A trivial observation wrapper's original callee is the proof kernel.
        if "_observe_" not in name and len(body.splitlines()) < 10 and len(internal_calls) == 1:
            target = internal_calls[0]
        ll = generated / (name + ".ll")
        mlir = generated / (name + ".mlir")
        extract_command = [args.llvm_bin / "llvm-extract", "--keep-const-init", "--func=" + target, "-S", llvm_ir, "-o", ll]
        optimize = "_observe_" in name and bool(internal_calls)
        if optimize:
            extract_command.insert(1, "--recursive")
        run(extract_command)
        if optimize:
            before = generated / (name + ".before-inline.ll")
            shutil.copyfile(ll, before)
            run([args.llvm_bin / "opt", "-S", "--passes=internalize,inline,function(sroa,instcombine,simplifycfg),globaldce",
                 "--internalize-public-api-list=" + name, "--inline-threshold=100000", before, "-o", ll])
        else:
            # --keep-const-init also retains unrelated constants. Remove only
            # definitions unreachable from this exported kernel; its body is
            # unchanged, and called external declarations remain declarations.
            run([args.llvm_bin / "opt", "-S", "--passes=internalize,globaldce",
                 "--internalize-public-api-list=" + target, ll, "-o", ll])
        run([args.llvm_bin / "mlir-translate", "--import-llvm", "--mlir-print-op-generic", ll, "-o", mlir])
        text = mlir.read_text()
        operations = collections.Counter(re.findall(r'"((?:llvm|x86vector)\.[^"]+)"\(', text))
        entry = {"wrapper": name, "target_symbol": target,
                 "llvm_inlining_applied": optimize,
                 "llvm_definition_count": len(functions(ll.read_text())),
                 "mlir_operations": dict(sorted(operations.items())),
                 "files_sha256": {p.name: sha(p) for p in [ll, mlir]}}
        if optimize:
            entry["files_sha256"][before.name] = sha(before)
        inventory[name] = entry
    inputs = ["source-manifest.json", "Cargo.extract.toml", "Cargo.extract.lock", "extract.py"]
    inputs += [name for name in wrapper_modules if (HERE / name).exists()]
    manifest.update({"rustc": rustc_version, "cargo": rust_version,
                     "mlir_translate": mlir_version, "commands": commands,
                     "features": FEATURES.split(","), "inputs_sha256": {p: sha(HERE / p) for p in inputs},
                     "crate_llvm_ir_sha256": sha(llvm_ir), "kernels": inventory,
                     "boundary": "Pinned complete crate source plus appended observation wrappers. Extraction manifest removes disabled optional and development dependencies; enabled dependency versions match Agave lock. Rust/LLVM compilation and MLIR import are trusted, not proved. LLVM-inlined observations are identified per kernel."})
    (generated / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Extracted {len(names)} kernels into {generated}")


if __name__ == "__main__":
    main()

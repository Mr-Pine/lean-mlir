#!/usr/bin/env python3
"""Extract the two width-five table constructors from the pinned crate IR.

The primary extraction intentionally leaves these callees external in the
double-base kernels. This supplemental extraction makes their exact bodies
available for a pointer/memory contract. It does not inline callees or rewrite
instructions. Recreate --crate-ir with extract.py and the primary manifest's
recorded Rust toolchain/commands; its SHA-256 must match that manifest.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


HERE = Path(__file__).resolve().parent
CFG_MANIFEST = HERE.parent / "Proof/DoubleBase/cfg-manifest.json"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_source():
    source_manifest = json.loads((HERE / "source-manifest.json").read_text())
    for name, expected in source_manifest["files_sha256"].items():
        path = HERE / "source" / name
        if sha(path) != expected:
            raise ValueError(f"source changed: {path}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--crate-ir", type=Path)
    parser.add_argument("--llvm-bin", type=Path)
    parser.add_argument("--llvm-lib", type=Path)
    parser.add_argument("--out", type=Path, default=HERE / "generated")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    primary_path = HERE / "generated/manifest.json"
    primary = json.loads(primary_path.read_text())
    verify_source()
    source_manifest_path = HERE / "source-manifest.json"
    if sha(source_manifest_path) != primary["inputs_sha256"]["source-manifest.json"]:
        raise ValueError("source manifest does not match the pinned primary extraction")
    args.out = args.out.resolve()
    target_manifest = args.out / "table-manifest.json"
    if args.check:
        manifest = json.loads(target_manifest.read_text())
        if manifest["primary_manifest_sha256"] != sha(primary_path):
            raise ValueError("primary extraction manifest changed")
        if manifest["source_manifest_sha256"] != sha(source_manifest_path):
            raise ValueError("source manifest changed")
        if manifest["script_sha256"] != sha(Path(__file__)):
            raise ValueError("table extraction script changed")
        if manifest["cfg_manifest_sha256"] != sha(CFG_MANIFEST):
            raise ValueError("double-base CFG manifest changed")
        for name, expected in manifest["files_sha256"].items():
            if sha(args.out / name) != expected:
                raise ValueError(f"extracted constructor changed: {name}")
        print("Pinned table-constructor extraction hashes verified")
        return
    if args.crate_ir is None or args.llvm_bin is None:
        parser.error("extraction requires --crate-ir and --llvm-bin")
    args.crate_ir = args.crate_ir.resolve()
    args.llvm_bin = args.llvm_bin.resolve()
    if sha(args.crate_ir) != primary["crate_llvm_ir_sha256"]:
        raise ValueError("crate LLVM IR does not match the pinned primary extraction")
    args.out.mkdir(parents=True, exist_ok=True)
    cfg = json.loads(CFG_MANIFEST.read_text())
    ir = args.crate_ir.read_text()
    definitions = set(re.findall(r"^define [^\n]*?@([^\s(]+)\(", ir, re.M))
    env = os.environ.copy()
    if args.llvm_lib:
        env["LD_LIBRARY_PATH"] = str(args.llvm_lib.resolve())
    commands = []

    def run(command):
        command = [str(x) for x in command]
        commands.append(command)
        subprocess.run(command, check=True, env=env)

    version = subprocess.check_output(
        [str(args.llvm_bin / "mlir-translate"), "--version"], env=env, text=True)
    if version != primary["mlir_translate"]:
        raise ValueError("MLIR importer version does not match the primary extraction")
    kernels = {}
    files = {}
    for backend in ("serial", "avx2"):
        targets = [name for name in cfg[backend]["callees"]
                   if "15NafLookupTable5" in name]
        if len(targets) != 1 or targets[0] not in definitions:
            raise ValueError(f"expected one defined {backend} width-five constructor: {targets}")
        target = targets[0]
        basename = f"agave_{backend}_table5"
        ll = args.out / (basename + ".ll")
        mlir = args.out / (basename + ".mlir")
        run([args.llvm_bin / "llvm-extract", "--keep-const-init", "--func=" + target,
             "-S", args.crate_ir, "-o", ll])
        run([args.llvm_bin / "opt", "-S", "--passes=internalize,globaldce",
             "--internalize-public-api-list=" + target, ll, "-o", ll])
        run([args.llvm_bin / "mlir-translate", "--import-llvm", "--mlir-print-op-generic",
             ll, "-o", mlir])
        extracted_definitions = re.findall(r"^define [^\n]*?@([^\s(]+)\(", ll.read_text(), re.M)
        if extracted_definitions != [target]:
            raise ValueError(f"unexpected extracted definitions: {extracted_definitions}")
        kernels[basename] = {
            "target_symbol": target,
            "signature": cfg[backend]["callees"][target],
            "llvm_inlining_applied": False,
            "llvm_definition_count": 1,
        }
        for path in (ll, mlir):
            files[path.name] = sha(path)
    manifest = {
        "crate": primary["crate"],
        "version": primary["version"],
        "registry_package_sha256": primary["registry_package_sha256"],
        "registry_vcs": primary["registry_vcs"],
        "primary_manifest_sha256": sha(primary_path),
        "source_manifest_sha256": sha(HERE / "source-manifest.json"),
        "cfg_manifest_sha256": sha(CFG_MANIFEST),
        "script_sha256": sha(Path(__file__)),
        "crate_llvm_ir_sha256": sha(args.crate_ir),
        "rustc": primary["rustc"],
        "mlir_translate": version,
        "tool_files_sha256": {
            name: sha(args.llvm_bin / name) for name in ("llvm-extract", "opt", "mlir-translate")
        },
        "tool_environment": {"LD_LIBRARY_PATH": env.get("LD_LIBRARY_PATH", "")},
        "commands": commands,
        "kernels": kernels,
        "files_sha256": files,
        "boundary": "Same crate LLVM IR as the primary pinned extraction. LLVM extraction, "
                    "dead-global elimination and MLIR import are trusted. Constructor bodies "
                    "are not inlined, optimized or rewritten; their external callees still "
                    "require independent execution contracts.",
    }
    target_manifest.write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Extracted two pinned table constructors into {args.out}")


if __name__ == "__main__":
    main()

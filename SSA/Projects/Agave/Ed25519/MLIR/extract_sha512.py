#!/usr/bin/env python3
"""Extract the verifier callees from the already pinned complete crate LLVM IR.

The main extraction leaves `verify_dalek` external to its byte-input wrapper.
This supplementary extraction selects original definitions from exactly the
same full-crate LLVM file. No Rust body or LLVM instruction is synthesized.
The existing manifest remains unchanged and its complete-crate hash is checked
before any compiler command is run.
"""

import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent

SYMBOLS = {
    "agave_scalar_from_sha512": "_RNvNtCsjK63O35OHGN_14solana_ed255197ed_sigs18scalar_from_sha512",
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--crate-ir", type=Path)
    parser.add_argument("--llvm-bin", type=Path)
    parser.add_argument("--llvm-lib", type=Path)
    parser.add_argument("--out", type=Path, default=HERE / "generated")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    base = json.loads((HERE / "generated/manifest.json").read_text())
    output = args.out.resolve()
    manifest_path = output / "sha512-manifest.json"
    if args.check:
        supplement = json.loads(manifest_path.read_text())
        assert supplement["crate_llvm_ir_sha256"] == base["crate_llvm_ir_sha256"]
        assert supplement["base_manifest_sha256"] == sha(HERE / "generated/manifest.json")
        assert supplement["extraction_script_sha256"] == sha(Path(__file__))
        for name, entry in supplement["kernels"].items():
            assert entry["target_symbol"] == SYMBOLS[name]
            for filename, expected in entry["files_sha256"].items():
                assert sha(output / filename) == expected, filename
        print(f"Validated {len(supplement['kernels'])} additional SHA-512 artifacts")
        return
    parser.error("--crate-ir and --llvm-bin are required unless --check") if not (
        args.crate_ir and args.llvm_bin) else None
    assert sha(args.crate_ir) == base["crate_llvm_ir_sha256"], "wrong full-crate LLVM IR"
    original = args.crate_ir.read_text()
    definitions = {m[1]: m[0] for m in re.finditer(
        r"^define [^\n]*?@([^\s(]+)\([^\n]*\).*?^}", original, re.M | re.S)}
    env = os.environ.copy()
    if args.llvm_lib:
        env["LD_LIBRARY_PATH"] = str(args.llvm_lib.resolve())
    versions = {}
    for tool in ("llvm-extract", "opt", "mlir-translate"):
        versions[tool] = subprocess.check_output(
            [str(args.llvm_bin / tool), "--version"], text=True, env=env)
        assert "LLVM version 22." in versions[tool]
    output.mkdir(parents=True, exist_ok=True)
    commands = []
    inventory = {}
    for name, target in SYMBOLS.items():
        assert target in definitions, target
        ll, mlir = output / f"{name}.ll", output / f"{name}.mlir"
        for command in (
            [args.llvm_bin / "llvm-extract", "--keep-const-init", f"--func={target}",
             "-S", args.crate_ir, "-o", ll],
            [args.llvm_bin / "opt", "-S", "--passes=internalize,globaldce",
             f"--internalize-public-api-list={target}", ll, "-o", ll],
            [args.llvm_bin / "mlir-translate", "--import-llvm", "--mlir-print-op-generic",
             ll, "-o", mlir],
        ):
            command = [str(x) for x in command]
            commands.append(command)
            subprocess.run(command, check=True, env=env)
        body = mlir.read_text()
        inventory[name] = {
            "target_symbol": target,
            "original_definition_sha256": hashlib.sha256(definitions[target].encode()).hexdigest(),
            "llvm_inlining_applied": False,
            "mlir_operations": dict(sorted(Counter(re.findall(r'"(llvm\.[^"]+)"\(', body)).items())),
            "files_sha256": {p.name: sha(p) for p in (ll, mlir)},
        }
    supplement = {
        "base_manifest_sha256": sha(HERE / "generated/manifest.json"),
        "crate_llvm_ir_sha256": base["crate_llvm_ir_sha256"],
        "extraction_script_sha256": sha(Path(__file__)),
        "tools": versions,
        "commands": commands,
        "kernels": inventory,
        "boundary": "Original pinned Rust definitions selected from the identical complete crate LLVM artifact. No body rewrite or further inlining. Compilation and MLIR import remain trusted. External declarations retain explicit proof obligations.",
    }
    manifest_path.write_text(json.dumps(supplement, indent=2) + "\n")
    print(f"Extracted {len(inventory)} SHA-512 finalization definitions into {output}")


if __name__ == "__main__":
    main()

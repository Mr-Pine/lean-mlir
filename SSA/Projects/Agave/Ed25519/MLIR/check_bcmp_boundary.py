#!/usr/bin/env python3
"""Check the pinned LLVM declaration/call boundary, without selecting a libc.

This is a provenance check, not a proof of bcmp's bytewise specification.
Pass --crate-ir to additionally check the full extraction input. No compiler
output is rewritten and no deployment implementation is inferred.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re


BASE = Path(__file__).resolve().parent


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def declaration_only(text: str) -> str:
    declarations = re.findall(r"^declare i32 @bcmp\([^\n]+$", text, re.M)
    require(len(declarations) == 1, "Expected exactly one i32 bcmp declaration")
    require(not re.search(r"^define\b[^\n]*@bcmp\(", text, re.M),
            "A bcmp implementation has appeared; inspect it instead of assuming the ABI")
    declaration = declarations[0]
    require("(ptr captures(none), ptr captures(none), i64)" in declaration,
            "bcmp pointer or length ABI changed")
    attribute = re.search(r" #(\d+)$", declaration)
    require(attribute is not None, "Missing bcmp function attributes")
    group = re.search(r"^attributes #" + attribute.group(1) + r" = \{([^\n]+)\}$",
                      text, re.M)
    require(group is not None, "Missing bcmp attribute group")
    for item in ("nocallback", "nofree", "nounwind", "willreturn", "memory(argmem: read)"):
        require(item in group.group(1), f"Missing bcmp attribute: {item}")
    return declaration


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--crate-ir", type=Path)
    args = parser.parse_args()
    manifest = json.loads((BASE / "generated/verifier-manifest.json").read_text())
    kernel = manifest["kernels"]["agave_verify_dalek"]
    for filename, expected in kernel["files_sha256"].items():
        require(sha256(BASE / "generated" / filename) == expected,
                f"Pinned verifier artifact hash mismatch: {filename}")
    llvm = (BASE / "generated/agave_verify_dalek.ll").read_text()
    require('target triple = "x86_64-unknown-linux-gnu"' in llvm, "Target ABI changed")
    declaration = declaration_only(llvm)
    occurrences = [line.strip() for line in llvm.splitlines() if "@bcmp(" in line]
    require(len(occurrences) == 2, "Expected one call and one bcmp declaration")
    call = next((line for line in occurrences if "call i32 @bcmp" in line), "")
    require(call.startswith("%bcmp.i = call i32 @bcmp("), "Comparison call changed")
    require("dereferenceable(32) %expected_R.i" in call, "Left input changed")
    require("dereferenceable(64) %signature, i64 32)" in call,
            "Signature input or comparison length changed")
    uses = [line.strip() for line in llvm.splitlines() if "%bcmp.i" in line]
    require(uses == [call, "%_31.i = icmp eq i32 %bcmp.i, 0"],
            "The caller now observes more than the bcmp zero/nonzero distinction")
    require("%..i = select i1 %_31.i, i8 -1, i8 2" in llvm, "Return-code select changed")
    imported = json.loads((BASE / "generated/verifier-rir-manifest.json").read_text())
    require(imported["Dalek"]["callees"]["bcmp"] == {
        "field": "compareBytes", "args": [".ptr", ".ptr", ".bv 64"],
        "returns": [".bv 32"]}, "RIR external-call interface changed")
    print("Pinned verifier: declaration only; length 32; result used only by equality to zero")
    print(declaration)
    if args.crate_ir is not None:
        require(sha256(args.crate_ir) == manifest["crate_llvm_ir_sha256"],
                "Full crate LLVM input does not match the pinned extraction manifest")
        declaration_only(args.crate_ir.read_text())
        print("Pinned full crate LLVM: declaration only (SHA-256 checked)")
    print("The external bytewise ABI premise remains explicit; no linked implementation is proved")


if __name__ == "__main__":
    main()

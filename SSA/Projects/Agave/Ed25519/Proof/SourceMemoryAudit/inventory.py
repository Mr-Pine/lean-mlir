#!/usr/bin/env python3
"""Read-only lexical inventory of attributes in directly imported RIR bodies.

The inventory is evidence about source spelling, not a reachability, translation,
or LLVM refinement proof. --check verifies the frozen report without rewriting it.
Run from any directory; only this directory's inventory.json is ever written.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / "lean-toolchain").exists())
AGAVE = ROOT / "SSA/Projects/Agave/Ed25519"
FOCUS = [
    "agave_ed25519_verify", "agave_verify_dalek", "agave_scalar_reduce32",
    "agave_scalar_wide", "agave_scalar_from_sha512", "agave_subtle_black_box",
    "agave_scalar_montgomery_mul", "agave_sha512_compress_dispatch",
    "agave_sha512_compress_avx2",
]


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def summary(accesses):
    return {
        "operations": dict(sorted(Counter(a["operation"] for a in accesses).items())),
        "alignment_histogram": dict(sorted(Counter(str(a["alignment"]) for a in accesses).items())),
        "volatile_operations": dict(sorted(Counter(a["operation"] for a in accesses if a["volatile"]).items())),
        "orderings": dict(sorted(Counter(str(a["ordering"]) for a in accesses).items())),
    }


def lean_bodies(path):
    definitions = []
    current = None
    block = None
    index = 0
    for line_number, line in enumerate(path.read_text().splitlines(), 1):
        decl = re.match(r"\s*(execution_def|mlir_def)\s+(\S+)", line)
        region = re.match(r"\s*def\s+(\S+)\s*:.*:=\s*mlir_region%", line)
        if region:
            decl = (None, "mlir_region%", region[1])
        if decl:
            current = {"kind": decl[1], "declaration": decl[2],
                       "declaration_line": line_number, "accesses": [], "register_definitions": {}}
            definitions.append(current)
            block = None
        elif current and line.strip() == "}":
            current = None
        if not current:
            continue
        bb = re.match(r"\s*\^(bb\d+)\b", line)
        if bb:
            block, index = bb[1], 0
        op = re.search(r'"(llvm\.[^"]+)"\(', line)
        if not op:
            continue
        op_index = index
        index += 1
        result = re.match(r"\s*(%\w+)\s*=", line)
        if result:
            current["register_definitions"][result[1]] = (op[1], line_number, line.strip())
        if op[1] not in ("llvm.load", "llvm.store", "llvm.alloca"):
            continue
        align = re.search(r"\balignment = (\d+) : i64", line)
        ordering = re.search(r"\bordering = (\d+) : i64", line)
        operands = re.search(r'"llvm\.[^"]+"\(([^)]*)\)', line)[1].split(",")
        current["accesses"].append({
            "line": line_number, "block": block, "operation_index_zero_based": op_index,
            "operation": op[1].removeprefix("llvm."),
            "alignment": int(align[1]) if align else None,
            "volatile": bool(re.search(r"\bvolatile_?\b", line)),
            "ordering": int(ordering[1]) if ordering else 0,
            "pointer_register": operands[-1].strip() if op[1] != "llvm.alloca" else None,
            "source": line.strip(),
        })
    for definition in definitions:
        registers = definition.pop("register_definitions")
        def root(register, visited=()):
            if register in visited:
                return {"kind": "cycle", "register": register}
            if register not in registers:
                return {"kind": "argument_or_unknown", "register": register}
            operation, n, text = registers[register]
            if operation == "llvm.alloca":
                return {"kind": "alloca", "register": register, "line": n}
            if operation == "llvm.mlir.addressof":
                return {"kind": "global", "register": register, "line": n,
                        "symbol": re.search(r"global_name = @([^,>}]+)", text)[1].strip()}
            if operation in ("llvm.getelementptr", "llvm.bitcast"):
                base = re.search(r'"llvm\.[^"]+"\(([^,)]*)', text)[1].strip()
                return root(base, (*visited, register))
            return {"kind": "unresolved", "register": register, "line": n}
        for access in definition["accesses"]:
            if access["pointer_register"]:
                access["pointer_root"] = root(access["pointer_register"])
        definition["summary"] = summary(definition["accesses"])
    return definitions


def llvm_source(path):
    accesses = []
    for i, line in enumerate(path.read_text().splitlines(), 1):
        op = re.match(r"\s*(?:%[^=]+ = )?(load|store|alloca)\b", line)
        if not op:
            continue
        alignment = re.search(r"\balign (\d+)\b", line)
        accesses.append({"line": i, "operation": op[1],
            "alignment": int(alignment[1]) if alignment else None,
            "volatile": bool(re.search(r"\bvolatile\b", line)),
            "ordering": "atomic" if re.search(r"\batomic\b", line) else 0,
            "source": line.strip()})
    return {"path": str(path.relative_to(ROOT)), "sha256": digest(path),
            "summary": summary(accesses), "accesses": accesses}


def build():
    files = []
    for directory in (AGAVE / "Proof", AGAVE / "Bridge/FiredancerSHAExecution"):
        for path in sorted(directory.rglob("*.lean")):
            if HERE in path.parents:
                continue  # Exclude this audit's synthetic erasure witnesses.
            definitions = lean_bodies(path)
            represented = {a["line"] for d in definitions for a in d["accesses"]}
            actual = {n for n, line in enumerate(path.read_text().splitlines(), 1)
                      if re.search(r'"llvm\.(load|store|alloca)"\(', line)}
            if represented != actual:
                raise ValueError(f"Uninventoried access spelling in {path}: {sorted(actual-represented)}")
            if definitions:
                files.append({"path": str(path.relative_to(ROOT)), "sha256": digest(path),
                              "definitions": definitions})
    all_accesses = [a for f in files for d in f["definitions"] for a in d["accesses"]]
    selected = []
    missing_focus = []
    for name in FOCUS:
        path = AGAVE / "MLIR/generated" / (name + ".ll")
        if path.exists():
            selected.append(llvm_source(path))
        else:
            missing_focus.append(name)
    selected.extend(llvm_source(path) for path in sorted(
        (AGAVE / "Bridge/FiredancerSHAExecution/generated").glob("fd_sha512_*.ll")))
    semantics = ["SSA/Projects/RIR/Syntax/Translate.lean", "SSA/Projects/RIR/Instruction.lean",
        "SSA/Projects/RIR/Memory/Pointer.lean", "SSA/Projects/RIR/Global.lean",
        "SSA/Projects/RIR/Semantics/Operations/Memory.lean",
        "SSA/Projects/RIR/Semantics/Effectful/Memory/Fits.lean",
        "SSA/Projects/Agave/Ed25519/Proof/Reduce64/Execution/Memory.lean"]
    return {
        "schema": 1,
        "scope": "Every direct execution_def/mlir_def/mlir_region% body in Agave Ed25519 Proof and Bridge/FiredancerSHAExecution, excluding SourceMemoryAudit's synthetic witnesses. Includes observation slices, alternate kernels and duplicated CFG presentations; counts are syntactic, not dynamic execution counts or a transitive call-reachability claim. LLVM focus is explicitly listed separately. pointer_root only traces syntactic GEP/bitcast chains; it is not a provenance proof.",
        "instruction_index": "Zero-based quoted llvm operation index within the source block, including constants and declarations; not a claim about erased RIR instruction positions.",
        "semantics_sha256": {p: digest(ROOT / p) for p in semantics},
        "imported_file_count": len(files), "imported_definition_count": sum(len(f["definitions"]) for f in files),
        "imported_summary": summary(all_accesses), "imported_files": files,
        "llvm_focus": selected, "missing_focus_names": missing_focus,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    output = HERE / "inventory.json"
    report = build()
    if args.check:
        if json.loads(output.read_text()) != report:
            raise SystemExit("Source attribute inventory differs; inspect source changes before regenerating")
    else:
        output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ("imported_file_count", "imported_definition_count", "imported_summary", "missing_focus_names")}, indent=2))


if __name__ == "__main__":
    main()

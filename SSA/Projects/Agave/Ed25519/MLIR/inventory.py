#!/usr/bin/env python3
"""Compare executable operation names and parameter forms to an RIR translator."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--translator", type=Path, required=True)
    parser.add_argument("--baseline", required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    translator = args.translator.read_text()
    supported = set(re.findall(r'"((?:llvm|x86vector)\.[^"]+)"', translator))
    manifest = json.loads((ROOT / "generated/manifest.json").read_text())
    kernels = {}
    for name, entry in manifest["kernels"].items():
        text = (ROOT / "generated" / (name + ".mlir")).read_text()
        lines = text.splitlines()
        start = next(i for i, line in enumerate(lines)
                     if '"llvm.func"' in line and f'sym_name = "{entry["target_symbol"]}"' in line)
        end = next(i for i in range(start + 1, len(lines)) if lines[i].startswith("  }) :"))
        body = "\n".join(lines[start + 1:end])
        operations = set(re.findall(r'"((?:llvm|x86vector)\.[^"]+)"\(', body))
        constants = set(re.findall(r'(%\d+) = "llvm.mlir.constant"', body))
        indexed = [line for line in body.splitlines()
                   if '"llvm.getelementptr"' in line and "-2147483648" in line]
        dynamic = []
        for line in indexed:
            operands = re.search(r'"llvm.getelementptr"\((.*?)\)', line).group(1).split(", ")
            if any(index not in constants for index in operands[1:]):
                dynamic.append(line)
        kernels[name] = {
            "unknown_operation_names": sorted(operations - supported),
            "gep_with_ssa_index_count": len(indexed),
            "gep_with_nonconstant_ssa_index_count": len(dynamic),
            "integer_overflow_flag_values": sorted(set(map(int, re.findall(r"overflowFlags = (\d+) : i32", body)))),
            "vector_width_cast_count": len(re.findall(r'"llvm\.(?:zext|sext|trunc)"[^\n]*vector<', body)),
        }
    report = {
        "baseline": args.baseline,
        "translator_sha256": hashlib.sha256(translator.encode()).hexdigest(),
        "scope": "Only the selected executable function body is compared, excluding module/global initializer operations. Operation-name recognition is not a proof of importability; operand types, flags, and semantics require separate validation. Integer overflow flags, vector width casts, and SSA GEP indices are reported separately.",
        "kernels": kernels,
    }
    args.out.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Check the exact MLIR blocks embedded in the reduction RIR program.

Only the enclosing module/function shell is omitted. All block operations,
attributes (including overflow flags), operand/result types, and return values
must match the LLVM22 importer output byte for byte.
"""
from pathlib import Path
import re

root = Path(__file__).resolve().parent
program = (root / "ReduceProgram.lean").read_text()
for i in range(5):
    mlir = (root.parent / "MLIR" / "generated" /
            f"agave_avx2_field_reduce_observe_{i}.mlir").read_text()
    expected = mlir[mlir.index("  ^bb0"):mlir.index("  }) : () -> ()")]
    actual = re.search(rf"mlir_def observe{i} :=\n\{{\n(.*?)\}}\n", program, re.S)
    if actual is None or actual.group(1) != expected:
        raise SystemExit(f"observe{i}: embedded block differs from generated MLIR")
print("All five reduction observer blocks exactly match generated MLIR.")

#!/usr/bin/env python3
"""Require exact compiler regions modulo the project's two syntax normalizations."""
import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent
ED25519 = HERE.parent.parent
spec = importlib.util.spec_from_file_location("ed25519_verify", ED25519 / "MLIR/verify.py")
verify = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verify)

for lean_name, kernel in [
    ("Double", "double"), ("CachedAdd", "cached_add"),
    ("CachedSub", "cached_sub"), ("AffineAdd", "affine_add"),
    ("AffineSub", "affine_sub"),
]:
    lifted = HERE / (lean_name + "Program.lean")
    original = ED25519 / "MLIR/generated" / ("agave_serial_point_" + kernel + ".mlir")
    assert verify.normalized_region(lifted.read_text()) == verify.normalized_region(original.read_text()), \
        f"Compiler-region mismatch: {lifted}"
print("Validated all five serial point RIR regions against compiler output.")

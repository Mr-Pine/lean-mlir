#!/usr/bin/env python3
"""Check pinned source, wrapper, compiler provenance, and generated artifact hashes."""
import hashlib
import json
from pathlib import Path
import re
from collections import Counter

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalized_region(text):
    """Normalize only flag spelling and GEPs with one literal SSA index.

    Every other token, SSA name, instruction and attribute must match. The GEP
    normalization is restricted to byte offsets and checks the constant's type.
    """
    match = re.search(r"(\^bb0\([^\n]*\):\n.*?)(?=\n\s*\})", text, re.S)
    assert match, "single-block region missing"
    region = match.group(1)
    constants = {name: (value, width) for name, value, width in re.findall(
        r'(%\d+) = "llvm.mlir.constant"\(\) <\{value = (-?\d+) : i(\d+)\}>', region)}
    region = re.sub(r"overflowFlags = #llvm\.overflow<(none|nsw|nuw)>",
                    lambda m: "overflowFlags = " + {"none": "0", "nsw": "1", "nuw": "2"}[m.group(1)] + " : i32", region)
    region = re.sub(r"overflowFlags = \[#llvm\.overflow<nsw>,\s*#llvm\.overflow<nuw>\]",
                    "overflowFlags = 3 : i32", region)
    region = re.sub(r"overflowFlags = #llvm\.overflow<nsw,\s*nuw>",
                    "overflowFlags = 3 : i32", region)
    lines = []
    for line in region.splitlines():
        if '"llvm.getelementptr"' in line:
            gep = re.search(r'"llvm.getelementptr"\((%\w+), (%\d+)\)(.*?)rawConstantIndices = array<i32: -2147483648>(.*?) : \(!llvm.ptr, i(\d+)\)', line)
            if gep:
                pointer, index, before, after, width = gep.groups()
                assert "elem_type = i8," in before, "only byte GEP normalization is allowed"
                value, constant_width = constants[index]
                assert width == constant_width
                assert -(2**31) < int(value) < 2**31
                line = line[:gep.start()] + f'"llvm.getelementptr"({pointer}){before}rawConstantIndices = array<i32: {value}>{after} : (!llvm.ptr)' + line[gep.end():]
        lines.append(" ".join(line.split()))
    return "\n".join(lines)


def main():
    original = json.loads((ROOT / "source-manifest.json").read_text())
    assert original["registry_package_sha256"] == "ff4c7caf3fe3d70815869a5838ee45b4d2b009eaacea1790ef3cd9b3c89edbbd"
    assert original["version"] == "0.2.4"
    for path, expected in original["files_sha256"].items():
        assert sha(ROOT / "source" / path) == expected, f"source changed: {path}"
    manifest = json.loads((ROOT / "generated/manifest.json").read_text())
    assert manifest["files_sha256"] == original["files_sha256"]
    assert "release: 1.98.1\n" in manifest["rustc"]
    assert "LLVM version: 22.1.8\n" in manifest["rustc"]
    for path, expected in manifest["inputs_sha256"].items():
        assert sha(ROOT / path) == expected, f"extraction input changed: {path}"
    observed = 0
    stack_observations = 0
    for name, entry in manifest["kernels"].items():
        for path, expected in entry["files_sha256"].items():
            assert sha(ROOT / "generated" / path) == expected, f"generated artifact changed: {path}"
        if "_observe_" in name:
            ir = (ROOT / "generated" / (name + ".ll")).read_text()
            assert entry["llvm_definition_count"] == 1, name
            effects = re.findall(r"\b(?:alloca|load|store|call|invoke)\b", ir)
            if name in {f"agave_serial_field_from_bytes_observe_{i}" for i in (1, 2, 3)}:
                assert Counter(effects) == Counter({"alloca": 1, "store": 2, "load": 1, "call": 2}), name
                calls = re.findall(r"\bcall [^\n]*?@([^\s(]+)", ir)
                assert set(calls) == {"llvm.lifetime.start.p0", "llvm.lifetime.end.p0"}, name
                stack_observations += 1
            else:
                assert not effects, f"observation is not pure: {name}"
                observed += 1
    lift = ROOT.parent / "Proof/SerialFieldMul/Lift.lean"
    if lift.exists():
        original_region = normalized_region((ROOT / "generated/agave_serial_field_mul.mlir").read_text())
        lifted_region = normalized_region(lift.read_text())
        assert original_region == lifted_region, "SerialFieldMul lift differs from generated compiler region"
    print(f"Validated {len(original['files_sha256'])} archived source files, "
          f"{len(manifest['kernels'])} extracted kernels, {observed} pure observations, "
          f"and {stack_observations} bounded stack observations.")


if __name__ == "__main__":
    main()

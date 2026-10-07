#!/usr/bin/env python3
"""Import pinned SHA-512 K64 and cold cache data without consulting the spec.

K64 is read independently from both original extracted LLVM backends. The
mutable cache becomes external after extraction; its original definition is
retained and hashed in the existing compression extraction manifest.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
GENERATED = ROOT / "MLIR/generated"
SYMBOL = "alloc_448aca044373cb4cde6849f95106f1ce"
CACHE = "_RNvNtNtCs7dqAOVfn11v_4sha26sha51210avx2_cpuid7STORAGE.0"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def llvm_bytes(value):
    result = bytearray()
    i = 0
    while i < len(value):
        if value[i] == "\\":
            if value[i + 1] in '\\"':
                result.append(ord(value[i + 1]))
                i += 2
            else:
                result.append(int(value[i + 1:i + 3], 16))
                i += 3
        else:
            result.append(ord(value[i]))
            i += 1
    return bytes(result)


def generate():
    manifest_path = GENERATED / "sha512-compress-manifest.json"
    manifest = json.loads(manifest_path.read_text())
    records = []
    values = []
    for kernel in ("agave_sha512_compress_dispatch", "agave_sha512_compress_avx2"):
        source = GENERATED / (kernel + ".ll")
        record = manifest["kernels"][kernel]
        assert sha(source.read_bytes()) == record["files_sha256"][source.name]
        matches = re.findall(r'^@' + SYMBOL + r' = internal unnamed_addr constant \[640 x i8\] c"(.*?)", align 8$', source.read_text(), re.M)
        assert len(matches) == 1
        data = llvm_bytes(matches[0])
        assert len(data) == 640
        original = record["original_global_definitions"][SYMBOL]
        assert sha(original["definition"].encode()) == original["sha256"]
        original_match = re.fullmatch(r'@' + SYMBOL + r' = private unnamed_addr constant \[640 x i8\] c"(.*?)", align 8', original["definition"])
        assert original_match and llvm_bytes(original_match[1]) == data
        values.append(data)
        records.append({"file": str(source.relative_to(ROOT)), "sha256": sha(source.read_bytes()), "original_definition_sha256": original["sha256"]})
    assert values[0] == values[1]
    cache = manifest["kernels"]["agave_sha512_compress_dispatch"]["original_global_definitions"][CACHE]
    assert cache["definition"] == f"@{CACHE} = internal unnamed_addr global i8 -1, align 1"
    assert sha(cache["definition"].encode()) == cache["sha256"]
    verifier_manifest_path = GENERATED / "verifier-rir-manifest.json"
    verifier = json.loads(verifier_manifest_path.read_text())
    iv_record, = [r for r in verifier["byteGlobals"] if r["lean_name"] == "sha512InitialState"]
    iv_source = GENERATED / iv_record["source"]
    assert sha(iv_source.read_bytes()) == verifier["Challenge"]["source_sha256"]
    extractor_path = ROOT.parent.parent / "RIR/Tools/extract_byte_globals.py"
    extractor_spec = importlib.util.spec_from_file_location("sha_initializer_bytes", extractor_path)
    extractor = importlib.util.module_from_spec(extractor_spec)
    extractor_spec.loader.exec_module(extractor)
    iv_extracted, = extractor.extract(iv_source.read_text(), [iv_record["symbol"]])
    assert all(iv_record[key] == value for key, value in iv_extracted.items())
    iv_bytes = bytes.fromhex(iv_record["bytes_hex"])
    assert len(iv_bytes) == 64 and sha(iv_bytes) == iv_record["sha256"]
    iv_import = ROOT / "Proof/Verifier/ExecutionGlobals.lean"
    iv_literal = "0x" + iv_bytes[::-1].hex()
    iv_definition = f'  ⟨"{iv_record["symbol"]}", 64, {iv_literal}, 16, by decide⟩'
    assert 'def sha512InitialState : ByteGlobal :=\n' + iv_definition in iv_import.read_text()
    data = values[0]
    content = f'''import SSA.Projects.RIR.Global

/-! Exact pinned initializers imported by import_initializer_data.py.
K64 is extracted independently of CompressionSpec.constants. The cold cache
initializer is from the original LLVM definition retained by the extractor;
the extracted compression module only declares that mutable global external.
See initializer-data-manifest.json for source and initializer hashes. -/
namespace Agave.Ed25519.SHA512.InitializerData
open LeanMLIR.RIR

-- Initializer SHA-256: {sha(data)}
def k64Bytes : BitVec 5120 := 0x{data[::-1].hex()}

def k64Global : ByteGlobal :=
  ⟨"{SYMBOL}", 640, k64Bytes, 8, by decide⟩

def coldCacheGlobal : ByteGlobal :=
  ⟨"{CACHE}", 1, 255, 1, by decide⟩

end Agave.Ed25519.SHA512.InitializerData
'''
    evidence = {"inputs": records, "source_manifest_sha256": sha(manifest_path.read_bytes()), "k64_symbol": SYMBOL, "initializer_sha256": sha(data), "initializer_length": len(data), "cache_original_definition": cache, "iv": {"record": iv_record, "source_sha256": sha(iv_source.read_bytes()), "import_sha256": sha(iv_import.read_bytes()), "extractor_sha256": sha(extractor_path.read_bytes())}, "generator_sha256": sha(Path(__file__).read_bytes()), "output_sha256": sha(content.encode()), "normalizations": []}
    return content, json.dumps(evidence, indent=2) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    source, manifest = generate()
    outputs = ((HERE / "InitializerData.lean", source), (HERE / "initializer-data-manifest.json", manifest))
    for path, expected in outputs:
        if args.check:
            assert path.read_text() == expected, f"stale {path}"
        else:
            path.write_text(expected)
    print("Validated both pinned K64 globals, the original cold-cache initializer, and the imported IV")


if __name__ == "__main__":
    main()

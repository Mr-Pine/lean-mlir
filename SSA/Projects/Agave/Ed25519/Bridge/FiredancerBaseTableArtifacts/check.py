#!/usr/bin/env python3
"""Check the extraction binding; Lean independently checks the mathematics.

With --source-checkout, also compare all recorded C inputs against the pinned
Git commit. With --reextract, compile that commit in a temporary directory and
compare both the LLVM and MLIR initializer values against the retained bytes.
This checker and the compiler/importer are outside Lean's trusted kernel.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tarfile
import tempfile


HERE = Path(__file__).resolve().parent
SYMBOL = "fd_ed25519_base_point_wnaf_table"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def llvm_words(text):
    lines = [line for line in text.splitlines() if line.startswith("@" + SYMBOL + " =")]
    require(len(lines) == 1, "expected exactly one LLVM initializer")
    require("[128 x %struct.fd_curve25519_edwards]" in lines[0], "unexpected LLVM table type")
    words = [int(value) for value in re.findall(r"i64 (-?\d+)", lines[0])]
    require(len(words) == 2560 and all(0 <= word < 2**64 for word in words), "unexpected LLVM words")
    return words


def mlir_words(text):
    """Interpret the retained global's constant/undef/insertvalue initializer."""
    start = text.index('sym_name = "' + SYMBOL + '"')
    start = text.index("({\n", start) + 3
    end = text.index("  }) : () -> ()", start)
    values = {}
    result = None
    for line in text[start:end].splitlines():
        ret = re.fullmatch(r'\s*"llvm.return"\((%\d+)\).*', line)
        if ret:
            result = values[ret[1]]
            continue
        match = re.fullmatch(r'\s*(%\d+) = "([^"]+)"\(([^)]*)\)(.*)', line)
        require(match is not None, "unexpected MLIR initializer operation: " + line)
        name, operation, arguments, tail = match.groups()
        if operation == "llvm.mlir.constant":
            dense = re.search(r"dense<\[([^]]+)\]> : tensor<5xi64>", tail)
            require(dense is not None, "unexpected MLIR constant")
            words = [int(value.strip()) for value in dense[1].split(",")]
            require(len(words) == 5, "unexpected MLIR coordinate size")
            values[name] = {(i,): word for i, word in enumerate(words)}
        elif operation == "llvm.mlir.undef":
            values[name] = {}
        elif operation == "llvm.insertvalue":
            base, value = arguments.split(", ")
            position = re.search(r"position = array<i64: ([^>]+)>", tail)
            require(position is not None, "missing MLIR insert position")
            path = tuple(int(i.strip()) for i in position[1].split(","))
            values[name] = {key: val for key, val in values[base].items()
                            if key[:len(path)] != path}
            values[name].update({path + key: val for key, val in values[value].items()})
        else:
            raise ValueError("unsupported MLIR initializer operation: " + operation)
    expected = [(k, c, 0, 0, i) for k in range(128) for c in range(4) for i in range(5)]
    require(result is not None and set(result) == set(expected), "incomplete MLIR initializer")
    return [result[key] for key in expected]


def source_words(text):
    body = text.split(SYMBOL + "[128] = {", 1)[1].split("\n};", 1)[0]
    body = re.sub(r"//[^\n]*", "", body)
    return [int(value, 16) for value in re.findall(r"0x([0-9a-fA-F]+)", body)]


def raw_bytes(words):
    return b"".join(word.to_bytes(8, "little") for word in words)


def run(args, **kwargs):
    return subprocess.check_output(args, **kwargs)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-checkout", type=Path)
    parser.add_argument("--reextract", action="store_true")
    parser.add_argument("--clang", default="clang")
    parser.add_argument("--llvm-extract", default="llvm-extract")
    parser.add_argument("--mlir-translate", default="mlir-translate")
    args = parser.parse_args()
    manifest = json.loads((HERE / "manifest.json").read_text())
    for name, expected in manifest["artifacts_sha256"].items():
        require(hashlib.sha256((HERE / name).read_bytes()).hexdigest() == expected,
                "artifact hash mismatch: " + name)
    data = (HERE / "table.bin").read_bytes()
    require(len(data) == 20480, "unexpected byte length")
    require(hashlib.sha256(data).hexdigest() == manifest["raw_initializer_sha256"], "byte hash mismatch")
    for name, decoder in [("source-table.c", source_words), ("table.ll", llvm_words), ("table.mlir", mlir_words)]:
        require(raw_bytes(decoder((HERE / name).read_text())) == data, "initializer mismatch: " + name)
    lean_path = HERE.parent / "FiredancerBaseTableData.lean"
    require(hashlib.sha256(lean_path.read_bytes()).hexdigest() == manifest["lean_data_sha256"],
            "Lean data hash mismatch")
    lean = lean_path.read_text()
    match = re.search(r"def bytes : BitVec 163840 := 0x([0-9a-f]+)#163840", lean)
    require(match is not None, "missing Lean byte definition")
    require(int(match[1], 16).to_bytes(20480, "little") == data, "Lean initializer mismatch")
    if args.source_checkout:
        for name, expected in manifest["source_files_sha256"].items():
            name = os.path.normpath(name)
            actual = run(["git", "-C", str(args.source_checkout), "show",
                          manifest["source_commit"] + ":" + name])
            require(hashlib.sha256(actual).hexdigest() == expected, "source hash mismatch: " + name)
    if args.reextract:
        require(args.source_checkout is not None, "--reextract requires --source-checkout")
        with tempfile.TemporaryDirectory(prefix="fd-base-table-") as directory:
            root = Path(directory)
            archive = root / "source.tar"
            with archive.open("wb") as output:
                subprocess.run(["git", "-C", str(args.source_checkout), "archive",
                                manifest["source_commit"], "src"], stdout=output, check=True)
            with tarfile.open(archive) as source:
                source.extractall(root, filter="data")
            run([args.clang, "-S", "-emit-llvm", "-O1", "-fno-vectorize", "-fno-slp-vectorize",
                 "-fno-unroll-loops", "-DFD_HAS_AVX=0", "-DFD_HAS_AVX512=0", "-o",
                 str(root / "curve.ll"), str(root / manifest["translation_unit"])])
            run([args.llvm_extract, "--keep-const-init", "--glob=" + SYMBOL, "-S",
                 str(root / "curve.ll"), "-o", str(root / "table.ll")])
            run([args.mlir_translate, "--import-llvm", "--mlir-print-op-generic",
                 str(root / "table.ll"), "-o", str(root / "table.mlir")])
            require(raw_bytes(llvm_words((root / "table.ll").read_text())) == data,
                    "recompiled LLVM initializer differs")
            require(raw_bytes(mlir_words((root / "table.mlir").read_text())) == data,
                    "reimported MLIR initializer differs")
    print("Verified 128 entries / 2560 limbs / 20480 bytes: C = LLVM = MLIR = binary = Lean.")
    print("Initializer SHA-256:", manifest["raw_initializer_sha256"])


if __name__ == "__main__":
    main()

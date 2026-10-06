#!/usr/bin/env python3
"""Import the exact verifier regions into RIR, without instruction normalization.

Each symbol gets a named, exactly typed primitive boundary. The generated
`execution_def` declarations check that import succeeds for all primitive
implementations and global addresses. They are not execution refinements.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
TARGET = HERE.parent / "Proof/SHA512/ExecutionProgram.lean"
GLOBALS_TARGET = HERE.parent / "Proof/SHA512/UnusedGlobals.lean"

REGIONS = {"SHA512Finalization": "agave_scalar_from_sha512"}

NAMES = {
    "12verify_dalek": "verifyDalek",
    "E8try_from": "keyFromBytes",
    "Signature10from_bytes": "signatureFromBytes",
    "16challenge_scalar": "challengeScalar",
    "12mul_by_pow_2": "pointMulByPow2",
    "NtCsh8VEmffyqhs_6subtle14ConstantTimeEq5ct_eq": "pointConstantTimeEq",
    "18CompressedEdwardsY10decompress": "decompress",
    "9black_boxhECsjK63O35OHGN_14solana_ed25519": "blackBoxByte",
    "6Scalar6reduce": "scalarReduce",
    "ConstantTimeEq5ct_eqCsjK63O35OHGN_14solana_ed25519": "bytesConstantTimeEq",
    "8init_get10init_inner": "initializeAvx2Cache",
    "6serial10scalar_mul19vartime_double_base3mul": "serialDoubleBase",
    "9spec_avx23mul9__impl_mul": "avx2DoubleBase",
    "12EdwardsPoint8compress": "compressPoint",
    "bcmp": "compareBytes",
    "sha51211compress512": "sha512Compress",
    "18scalar_from_sha512": "scalarFromSha512",
    "25from_bytes_mod_order_wide": "reduceWide",
}


def lean_type(ty):
    if ty == "!llvm.ptr":
        return ".ptr"
    assert re.fullmatch(r"i[0-9]+", ty), ty
    return f".bv {ty[1:]}"


def types(tys):
    return [] if tys == "()" else [lean_type(t) for t in tys.strip("()").split(", ")]


def symbol_spelling(symbol):
    """Lean's identifier grammar needs quotes for LLVM dotted numeric names."""
    return symbol if re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", symbol) else json.dumps(symbol)


def generate():
    lines = [
        "module", "", "public import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionElab", "",
        "/-! Exact pinned verifier regions. Regenerate with MLIR/import_sha512.py.",
        "", "Only required symbol-name quoting changes the source spelling. `execution_def`",
        "checks successful RIR translation, including calls and globals; it",
        "does not supply any primitive's semantics or prove an execution result.",
        "This is the original `scalar_from_sha512` body, including zeroization.",
        "-/", "", "namespace Agave.Ed25519.Verifier.Execution", "",
        "open LeanMLIR.RIR", "@[expose] public section", "",
    ]
    manifest = {}
    for namespace, kernel in REGIONS.items():
        source = HERE / "generated" / f"{kernel}.mlir"
        text = source.read_text()
        assert text.count("  ^bb0(") == 1
        start = text.index("  ^bb0(")
        end = text.index("\n  }) : () -> ()", start)
        body = text[start:end]
        calls = {}
        for line in body.splitlines():
            symbol = re.search(r"callee = @([^, >}]+)", line)
            if not symbol:
                continue
            args, rets = line.rsplit(" : ", 1)[1].split(" -> ")
            names = [name for suffix, name in NAMES.items() if symbol[1].endswith(suffix)]
            assert len(names) == 1, symbol[1]
            entry = {"field": names[0], "args": types(args), "returns": types(rets)}
            assert symbol[1] not in calls or calls[symbol[1]] == entry
            calls[symbol[1]] = entry
        globals_ = list(dict.fromkeys(re.findall(r"global_name = @([^, >}]+)", body)))
        lines += [f"namespace {namespace}", "", "structure Primitives where"]
        for symbol, entry in calls.items():
            lines += [f"  /-- Exact external symbol `{symbol}`. -/",
                      f"  {entry['field']} : Vals [{', '.join(entry['args'])}] → EffectM (Vals [{', '.join(entry['returns'])}])"]
        lines += ["", "def Primitives.resolve (p : Primitives) : String → Option Callee"]
        for symbol, entry in calls.items():
            lines += [f'  | "{symbol}" => some ⟨[{", ".join(entry["args"])}], [{", ".join(entry["returns"])}], p.{entry["field"]}⟩']
        lines += ["  | _ => none", ""]
        if globals_:
            lines += ["structure Globals where"]
            for i, symbol in enumerate(globals_):
                lines += [f"  /-- `{symbol}`; initializer and mutability are separate memory obligations. -/",
                          f"  address{i} : Pointer"]
            lines += ["", "def Globals.resolve (g : Globals) : String → Option Pointer"]
            for i, symbol in enumerate(globals_):
                lines += [f'  | "{symbol}" => some g.address{i}']
            lines += ["  | _ => none", ""]
        binders = "(p : Primitives)" + (" (g : Globals)" if globals_ else "")
        arguments = "p" + (" g" if globals_ else "")
        rendered_body = body
        quoted = []
        for symbol in [*calls, *globals_]:
            spelling = symbol_spelling(symbol)
            if spelling != symbol:
                rendered_body = rendered_body.replace("@" + symbol, "@" + spelling)
                quoted.append(symbol)
        lines += [f"execution_def program {binders} :=", "{", rendered_body, "}"]
        lines += ["with " + ",\n  ".join(f"@{symbol_spelling(symbol)} := p.{entry['field']}" for symbol, entry in calls.items())]
        if globals_:
            lines += ["globals " + ",\n  ".join(f"@{symbol_spelling(symbol)} := g.address{i}" for i, symbol in enumerate(globals_))]
        block_count = len(re.findall(r"^  \^bb\d", body, re.M))
        lines += ["", f"theorem block_count {binders} : (program {arguments}).n = {block_count} := rfl",
                  "", f"end {namespace}", ""]
        manifest[namespace] = {
            "source": str(source.relative_to(HERE)),
            "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "region_sha256": hashlib.sha256(body.encode()).hexdigest(),
            "region_lines": len(body.splitlines()),
            "callees": calls,
            "globals": globals_,
            "normalizations": [{"symbol_quoting": name} for name in quoted],
        }
    lines += ["end", "end Agave.Ed25519.Verifier.Execution", ""]
    global_lines = []
    manifest["import_inputs_sha256"] = {
        str(path.relative_to(HERE.parent)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in (Path(__file__), HERE.parent / "Proof/Verifier/ExecutionElab.lean")
    }
    return "\n".join(lines), "\n".join(global_lines), json.dumps(manifest, indent=2) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    source, globals_source, manifest = generate()
    path = HERE / "generated/sha512-rir-manifest.json"
    if args.check:
        assert TARGET.read_text() == source, f"stale {TARGET}"
        assert path.read_text() == manifest, f"stale {path}"
        print("Validated exact SHA-512 finalization RIR region")
    else:
        TARGET.write_text(source)
        path.write_text(manifest)


if __name__ == "__main__":
    main()

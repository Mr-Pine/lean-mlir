#!/usr/bin/env python3
"""Copy complete compiler-generated double-base regions into RIR AST definitions.

No instruction, flag, SSA identifier or branch is rewritten. Callee semantics
and global addresses are explicit parameters, not axioms. The resulting
`program` returns Except: successful import still needs to be established and
does not assert the primitive contracts or prove verifier correctness.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
GENERATED = HERE.parent.parent / "MLIR" / "generated"


def generate(mode):
    source = GENERATED / f"agave_{mode}_double_base.mlir"
    text = source.read_text()
    start = text.index("  ^bb0(")
    end = text.index("\n  }) : () -> ()", start)
    body = text[start:end]
    assert text.count("  ^bb0(") == 1
    calls = {}
    for line in body.splitlines():
        match = re.search(r"callee = @([^, >}]+)", line)
        if match:
            signature = line.rsplit(" : ", 1)[1]
            assert signature.endswith(" -> ()"), signature
            types = signature.removesuffix(" -> ()")[1:-1].split(", ")
            lean_types = [".ptr" if t == "!llvm.ptr" else f".bv {int(t[1:])}" for t in types]
            assert match[1] not in calls or calls[match[1]] == lean_types
            calls[match[1]] = lean_types
    globals_ = list(dict.fromkeys(re.findall(r"global_name = @([^, >}]+)", body)))
    ns = mode.title() + "CFG"
    output = [
        "module", "", "public import SSA.Projects.RIR.Syntax.Elab", "",
        "/-! Complete pinned compiler CFG, copied without instruction changes.",
        "Regenerate using import_cfg.py. The source MLIR and all source constants",
        "remain in MLIR/generated; the extraction manifest records provenance.",
        "",
        "`program` is a checked import attempt, not a successful-refinement theorem.",
        "Each external primitive has its exact call-site signature and each global",
        "address is explicit. Primitive behavior, memory separation, table contents,",
        "allocation invariants and termination remain independent proof obligations.",
        "-/", "", f"namespace Agave.Ed25519.DoubleBase.{ns}", "",
        "open LeanMLIR.RIR", "@[expose] public section", "",
        "structure Primitives where",
    ]
    for i, (name, types) in enumerate(calls.items()):
        output += [f"  /-- `{name}` -/",
                   f"  call{i} : Vals [{', '.join(types)}] → EffectM (Vals [])"]
    output += ["", "def Primitives.resolve (p : Primitives) : String → Option Callee"]
    for i, (name, types) in enumerate(calls.items()):
        output += [f'  | "{name}" => some ⟨[{", ".join(types)}], [], p.call{i}⟩']
    output += ["  | _ => none", "", "structure Globals where"]
    for i, name in enumerate(globals_):
        output += [f"  /-- `{name}`; its source initializer must be present in memory. -/",
                   f"  address{i} : Pointer"]
    output += ["", "def Globals.resolve (g : Globals) : String → Option Pointer"]
    for i, name in enumerate(globals_):
        output += [f'  | "{name}" => some g.address{i}']
    output += ["  | _ => none", "", "def region : MLIR.Region := mlir_region%", "{", body, "}", "",
               "def program (p : Primitives) (g : Globals) : Except String Func :=",
               "  translate region p.resolve g.resolve", "", "end", "",
               f"end Agave.Ed25519.DoubleBase.{ns}", ""]
    manifest = {
        "source": str(source.relative_to(HERE.parents[2])),
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "region_sha256": hashlib.sha256(body.encode()).hexdigest(),
        "region_lines": len(body.splitlines()),
        "callees": calls, "globals": globals_,
        "normalizations": [],
    }
    return HERE / f"{ns}.lean", "\n".join(output), manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    manifest = {}
    for mode in ("serial", "avx2"):
        target, content, entry = generate(mode)
        if args.check:
            assert target.read_text() == content, f"stale {target}"
        else:
            target.write_text(content)
        manifest[mode] = entry
    path = HERE / "cfg-manifest.json"
    content = json.dumps(manifest, indent=2) + "\n"
    if args.check:
        assert path.read_text() == content, f"stale {path}"
    else:
        path.write_text(content)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Import the original 32-byte subgroup scalar reduction region without rewrites.

The only external function is the already separately imported subtle::black_box
body. Arithmetic, zeroization, lifetime, allocation and flags remain verbatim.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
TARGET = HERE.parent / 'Proof/ScalarReduce32/Program.lean'
MANIFEST = HERE / 'generated/scalar-reduce32-rir-manifest.json'
SYMBOL = '_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar6reduce'
BLACK_BOX = '_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def generate():
    source = HERE / 'generated/agave_scalar_reduce32.mlir'
    text = source.read_text()
    assert text.count('  ^bb0(') == 1
    start = text.index('  ^bb0(')
    end = text.index('\n  }) : () -> ()', start)
    region = text[start:end]
    assert re.findall(r'callee = @([^, >}]+)', region) == [BLACK_BOX]
    assert not re.findall(r'global_name = @([^, >}]+)', region)
    extraction = json.loads((HERE / 'generated/scalar-reduce32-manifest.json').read_text())
    assert extraction['kernels']['agave_scalar_reduce32']['target_symbol'] == SYMBOL
    assert extraction['kernels']['agave_scalar_reduce32']['files_sha256'][source.name] == sha(source)
    prelude = '''module

public import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionElab
public import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.BlackBoxProgram

/-!
Exact pinned 32-byte scalar reduction body. Regenerate with
`MLIR/import_scalar_reduce32.py`. This is the callee of Dalek.scalarReduce,
not base-field Reduce64 and not the wide SHA-512 scalar reduction.

All source instructions and flags are retained; the sole external call is
linked to its independently imported black_box body. Import success alone
does not prove the arithmetic result, absence of poison, or memory frame.
-/
namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
@[expose] public section

'''
    lean = prelude + f'def sourceSymbol : String := "{SYMBOL}"\n\n'
    lean += 'execution_def program :=\n{\n' + region + '\n}\n'
    lean += f'with @{BLACK_BOX} :=\n  Encoding.Decompress.Execution.BlackBox.program.call\n\n'
    lean += 'theorem block_count : program.n = 1 := rfl\n\nend\nend Agave.Ed25519.ScalarReduce32.Execution\n'
    manifest = {
        'target_symbol': SYMBOL,
        'source': str(source.relative_to(HERE)),
        'source_sha256': sha(source),
        'extraction_manifest_sha256': sha(HERE / 'generated/scalar-reduce32-manifest.json'),
        'region_sha256': hashlib.sha256(region.encode()).hexdigest(),
        'region_lines': len(region.splitlines()),
        'normalizations': [],
        'linked_callees': {BLACK_BOX: 'Agave.Ed25519.Encoding.Decompress.Execution.BlackBox.program.call'},
        'operations': dict(sorted(Counter(re.findall(r'"(llvm\.[^"]+)"\(', region)).items())),
        'import_script_sha256': sha(Path(__file__)),
        'output_sha256': hashlib.sha256(lean.encode()).hexdigest(),
    }
    return lean, json.dumps(manifest, indent=2) + '\n'

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    lean, manifest = generate()
    if args.check:
        assert TARGET.read_text() == lean, f'stale {TARGET}'
        assert MANIFEST.read_text() == manifest, f'stale {MANIFEST}'
        print('Validated exact 32-byte scalar reduction RIR region')
    else:
        TARGET.parent.mkdir(parents=True, exist_ok=True)
        TARGET.write_text(lean)
        MANIFEST.write_text(manifest)

if __name__ == '__main__':
    main()

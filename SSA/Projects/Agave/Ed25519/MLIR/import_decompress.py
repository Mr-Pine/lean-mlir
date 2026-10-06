#!/usr/bin/env python3
"""Import exact decompression call-closure regions, retaining all attributes.

Regeneration checks the LLVM extraction manifest first. RIR import is not a
proof of execution conformance; the generated primitive records are explicit
links awaiting contracts or replacement by the separately imported bodies.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
TARGET = HERE.parent / 'Proof/Encoding/DecompressExecution'
REGIONS = {
    'Program': ('Decode', 'agave_point_decompress'),
    'SqrtRatioProgram': ('SqrtRatio', 'agave_field_sqrt_ratio_i'),
    'Pow22501Program': ('Pow22501', 'agave_field_pow22501'),
    'Pow2kProgram': ('Pow2k', 'agave_field_pow2k'),
    'ToBytesProgram': ('ToBytes', 'agave_field_to_bytes'),
    'BlackBoxProgram': ('BlackBox', 'agave_subtle_black_box'),
    'BytesEqProgram': ('BytesEq', 'agave_subtle_bytes_eq'),
}
NAMES = {
    'FieldElement5112sqrt_ratio_i': 'sqrtRatio',
    'FieldElement518pow22501': 'pow22501',
    'FieldElement515pow2k': 'pow2k',
    'FieldElement518to_bytes': 'toBytes',
    'Mul3mul': 'mul',
    '9black_boxhECsjK63O35OHGN_14solana_ed25519': 'blackBoxByte',
    'ShNtB5_14ConstantTimeEq5ct_eqCsjK63O35OHGN_14solana_ed25519': 'bytesEq',
}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def types(tys):
    if tys == '()':
        return []
    ans = []
    for ty in tys.strip('()').split(', '):
        if ty == '!llvm.ptr':
            ans.append('.ptr')
        else:
            assert re.fullmatch(r'i[0-9]+', ty), ty
            ans.append(f'.bv {ty[1:]}')
    return ans

def generate(module, namespace, kernel):
    source = HERE / 'generated' / f'{kernel}.mlir'
    text = source.read_text()
    assert text.count('  ^bb0(') == 1
    start = text.index('  ^bb0(')
    end = text.index('\n  }) : () -> ()', start)
    body = text[start:end]
    calls = {}
    for line in body.splitlines():
        symbol = re.search(r'callee = @([^, >}]+)', line)
        if not symbol:
            continue
        args, rets = line.rsplit(' : ', 1)[1].split(' -> ')
        names = [name for suffix, name in NAMES.items() if symbol[1].endswith(suffix)]
        assert len(names) == 1, symbol[1]
        entry = {'field': names[0], 'args': types(args), 'returns': types(rets)}
        assert symbol[1] not in calls or calls[symbol[1]] == entry
        calls[symbol[1]] = entry
    globals_ = list(dict.fromkeys(re.findall(r'global_name = @([^, >}]+)', body)))
    lines = ['module', '', 'public import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionElab', '',
        '/-! Exact pinned MLIR region. Regenerate with MLIR/import_decompress.py.',
        'All instructions and attributes are retained. Successful import is not an execution proof. -/', '',
        f'namespace Agave.Ed25519.Encoding.Decompress.Execution.{namespace}', '',
        'open LeanMLIR.RIR', '@[expose] public section', '']
    if calls:
        lines += ['structure Primitives where']
        for symbol, entry in calls.items():
            lines += [f'  /-- Exact external symbol `{symbol}`. -/',
                f"  {entry['field']} : Vals [{', '.join(entry['args'])}] → EffectM (Vals [{', '.join(entry['returns'])}])"]
        lines += ['']
    if globals_:
        lines += ['structure Globals where']
        for i, symbol in enumerate(globals_):
            lines += [f'  /-- Address of `{symbol}`; its exact initializer is a separate memory obligation. -/',
                      f'  address{i} : Pointer']
        lines += ['']
    binders = ('(p : Primitives)' if calls else '') + (' (g : Globals)' if globals_ else '')
    arguments = ('p' if calls else '') + (' g' if globals_ else '')
    lines += [f'execution_def program {binders} :=', '{', body, '}']
    if calls:
        lines += ['with ' + ',\n  '.join(f"@{symbol} := (p).{entry['field']}" for symbol, entry in calls.items())]
    if globals_:
        lines += ['globals ' + ',\n  '.join(f'@{symbol} := (g).address{i}' for i, symbol in enumerate(globals_))]
    blocks = len(re.findall(r'^  \^bb\d', body, re.M))
    lines += ['', f'theorem block_count {binders} : (program {arguments}).n = {blocks} := rfl', '',
              'end', f'end Agave.Ed25519.Encoding.Decompress.Execution.{namespace}', '']
    output = '\n'.join(lines)
    record = {'source': str(source.relative_to(HERE)), 'source_sha256': sha(source.read_bytes()),
        'region_sha256': sha(body.encode()), 'region_lines': len(body.splitlines()),
        'callees': calls, 'globals': globals_, 'normalizations': [], 'output_sha256': sha(output.encode())}
    return output, record

def generate_globals():
    extractor_path = HERE.parents[2] / 'RIR/Tools/extract_byte_globals.py'
    spec = importlib.util.spec_from_file_location('decompress_byte_globals', extractor_path)
    extractor = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(extractor)
    lines = ['module', '', 'public import SSA.Projects.RIR.Global', '',
        '/-! Exact constant initializers, generated by MLIR/import_decompress.py. -/', '',
        'namespace Agave.Ed25519.Encoding.Decompress.Execution', '',
        'open LeanMLIR.RIR', '@[expose] public section', '']
    records = []
    for name, file, symbol in (
        ('curveD', 'agave_point_decompress.mlir', 'alloc_781589f30b7aca1e8db8c1d787298044'),
        ('sqrtM1', 'agave_field_sqrt_ratio_i.mlir', 'alloc_4a840e2d409aa262ab906382f915ac1f'),
    ):
        record, = extractor.extract((HERE/'generated'/file).read_text(), [symbol])
        record['source'] = file
        record['lean_name'] = name
        records.append(record)
        bits = '0x' + bytes.fromhex(record['bytes_hex'])[::-1].hex()
        lines += [f"-- Source bytes SHA-256: {record['sha256']}",
            f'def {name} : ByteGlobal :=',
            f"  ⟨{json.dumps(symbol)}, {record['length']}, {bits}, {record['alignment']}, by decide⟩", '']
    lines += ['end', 'end Agave.Ed25519.Encoding.Decompress.Execution', '']
    return '\n'.join(lines), records

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    subprocess.run([sys.executable, str(HERE/'extract_decompress.py'), '--check'], check=True)
    records = {}
    TARGET.mkdir(parents=True, exist_ok=True)
    for module, (namespace, kernel) in REGIONS.items():
        source, records[module] = generate(module, namespace, kernel)
        target = TARGET / f'{module}.lean'
        if args.check:
            assert target.read_text() == source, f'stale {target}'
        else:
            target.write_text(source)
    globals_source, records['byteGlobals'] = generate_globals()
    globals_target = TARGET/'Globals.lean'
    if args.check:
        assert globals_target.read_text() == globals_source, f'stale {globals_target}'
    else:
        globals_target.write_text(globals_source)
    records['import_inputs_sha256'] = {
        str(path.relative_to(HERE.parent)): sha(path.read_bytes())
        for path in (Path(__file__), HERE.parent/'Proof/Verifier/ExecutionElab.lean')}
    manifest = json.dumps(records, indent=2) + '\n'
    target = HERE/'generated/decompress-rir-manifest.json'
    if args.check:
        assert target.read_text() == manifest, f'stale {target}'
        print('Validated seven exact decompression RIR regions')
    else:
        target.write_text(manifest)

if __name__ == '__main__':
    main()

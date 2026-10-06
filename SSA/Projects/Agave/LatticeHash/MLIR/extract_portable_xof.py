#!/usr/bin/env python3
"""Compile separate exact-body BLAKE3 XOF/in-place wrappers; preserve pre artifacts."""
import argparse
import hashlib
import json
import pathlib
import re
import subprocess

SOURCE_HASHES = {
    'portable.rs': '85ed8cd8f601e6801c0a26358c7ac70e29759445cfe39c584f40af072a201601',
    'lib.rs': 'a187904c4b12ea7c100557c0f167cc91a034e391ddeb56c9db65f7d400a4b566',
    'platform.rs': '954e3564bb976c333cfaa68fc672a8543afc2e021c8b89e8d9393816b0ad90d1',
}
SYMBOLS = ['agave_portable_compress_xof', 'agave_portable_compress_in_place']


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--blake3', type=pathlib.Path, required=True)
    parser.add_argument('--out', type=pathlib.Path, required=True)
    parser.add_argument('--rustc', required=True)
    parser.add_argument('--mlir-translate', required=True)
    args = parser.parse_args()
    sources = {name: (args.blake3 / 'src' / name).read_bytes() for name in SOURCE_HASHES}
    for name, expected in SOURCE_HASHES.items():
        if digest(sources[name]) != expected:
            raise ValueError(f'locked BLAKE3 source changed: {name}')
    rustc = subprocess.check_output([args.rustc, '--version', '--verbose'], text=True)
    mlir = subprocess.check_output([args.mlir_translate, '--version'], text=True)
    if 'release: 1.98.1\n' not in rustc or 'LLVM version: 22.1.8\n' not in rustc:
        raise ValueError('expected Rust 1.98.1 / LLVM 22.1.8')
    if not mlir.startswith('Ubuntu LLVM version 22.1.8\n'):
        raise ValueError('expected MLIR 22.1.8')
    spans = []

    def record(file, name, kind, start, end):
        fragment = sources[file][start:end]
        spans.append({'file': file, 'name': name, 'kind': kind,
                      'start_byte': start, 'end_byte': end, 'sha256': digest(fragment)})
        return fragment.decode('utf-8') + '\n'

    def function(file, name):
        source = sources[file]
        pattern = rb'^(?:pub(?:\([^)]*\))? )?fn ' + name.encode() + rb'\('
        matches = list(re.finditer(pattern, source, re.MULTILINE))
        if len(matches) != 1:
            raise ValueError(f'expected one exact function declaration: {file}:{name}')
        start = matches[0].start()
        brace = source.index(b'{', start)
        depth, end = 1, brace + 1
        while depth:
            depth += (source[end] == ord('{')) - (source[end] == ord('}'))
            end += 1
        # This attribute is harness instrumentation, outside the original span.
        return '#[inline(always)]\n' + record(file, name, 'function', start, end)

    def constant(name):
        source = sources['lib.rs']
        start = source.index(b'const ' + name.encode() + b':')
        end = source.index(b'];', source.index(b'=', start)) + 2
        return record('lib.rs', name, 'constant', start, end)

    harness = 'type CVWords = [u32; 8];\nconst BLOCK_LEN: usize = 64;\n'
    harness += constant('IV') + constant('MSG_SCHEDULE')
    harness += function('lib.rs', 'counter_low') + function('lib.rs', 'counter_high')
    harness += 'mod platform {\n'
    harness += function('platform.rs', 'words_from_le_bytes_64')
    harness += function('platform.rs', 'le_bytes_from_words_64') + '}\n'
    for name in ['g', 'round', 'compress_pre', 'compress_xof', 'compress_in_place']:
        harness += function('portable.rs', name)
    harness += '''
#[unsafe(no_mangle)]
pub fn agave_portable_compress_xof(cv:&CVWords, block:&[u8;64], len:u8,counter:u64,flags:u8)->[u8;64] { compress_xof(cv,block,len,counter,flags) }
#[unsafe(no_mangle)]
pub fn agave_portable_compress_in_place(cv:&mut CVWords, block:&[u8;64], len:u8,counter:u64,flags:u8) { compress_in_place(cv,block,len,counter,flags); }
'''
    args.out.mkdir(parents=True, exist_ok=True)
    rs = args.out / 'portable_xof_harness.rs'
    ll = args.out / 'portable_xof.ll'
    mlir_path = args.out / 'portable_xof.mlir'
    rs.write_text(harness)
    commands = [
        [args.rustc, '--edition=2024', '--crate-type=lib', '--crate-name=agave_portable_xof_extract',
         '--emit=llvm-ir', '-C', 'opt-level=3', '-C', 'panic=abort', '-C', 'debug-assertions=no',
         str(rs), '-o', str(ll)],
        [args.mlir_translate, '--import-llvm', '--mlir-print-op-generic', str(ll), '-o', str(mlir_path)],
    ]
    for command in commands:
        subprocess.run(command, check=True)
    manifest = {
        'source_hashes': SOURCE_HASHES, 'verbatim_spans': spans, 'symbols': SYMBOLS,
        'rustc': rustc, 'mlir_translate': mlir, 'commands': commands,
        'artifacts': {path.name: digest(path.read_bytes()) for path in [rs, ll, mlir_path]},
        'boundary': 'Exact locked BLAKE3 function bodies/constants, supplied CVWords/BLOCK_LEN aliases, '
                    'inline(always) attributes and exported wrappers. Original compress_pre remains inlined; '
                    'no call rebinding, synthetic IR, or full-crate compilation. Separate module preserves prior artifacts.',
    }
    (args.out / 'portable_xof_manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')


if __name__ == '__main__':
    main()

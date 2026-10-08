#!/usr/bin/env python3
"""Check the seven scalar C initializers against the Lean literals and manifest."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--firedancer', type=Path, default=Path('/home/nine/Documents/firedancer'))
    args = parser.parse_args()
    manifest = json.loads((HERE / 'field-initializer-manifest.json').read_text())
    sources = []
    for path, expected in manifest['files'].items():
        source = subprocess.check_output(['git', '-C', str(args.firedancer), 'show',
                                          f"{manifest['commit']}:{path}"])
        assert hashlib.sha256(source).hexdigest() == expected, path
        sources.append(source.decode())
    lean = (HERE / 'FiredancerFieldInitializer.lean').read_text()
    symbols = re.findall(r'"([^"]+)"', lean.split('def symbol', 1)[1].split('def limbs', 1)[0])
    limb_literals = re.findall(r'0x[0-9a-f]+', lean.split('def limbs', 1)[1].split('def bytes', 1)[0])
    assert symbols == list(manifest['constants'])
    assert len(limb_literals) == 35
    for i, name in enumerate(symbols):
        pattern = r'static const fd_f25519_t ' + name + r'\[1\] = \{\{(.*?)\}\};'
        matches = [m for source in sources if (m := re.search(pattern, source, re.S))]
        assert len(matches) == 1, name
        values = [int(v, 16) for v in re.findall(r'0x[0-9a-f]+', matches[0][1])]
        assert values == manifest['constants'][name]['limbs'], name
        assert values == [int(v, 16) for v in limb_literals[5*i:5*i+5]], name
        raw = b''.join(v.to_bytes(8, 'little') for v in values)
        assert raw.hex() == manifest['constants'][name]['little_endian_bytes_hex'], name
    print('PASS: seven pinned C initializers match the Lean 40-byte field constants')

if __name__ == '__main__':
    main()

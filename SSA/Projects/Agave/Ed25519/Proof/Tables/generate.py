#!/usr/bin/env python3
"""Regenerate kernel-certified odd-multiple tables from exact extracted MLIR globals.

All mathematical claims are proved in the emitted Lean source. Python checks are
early diagnostics only. The reviewed source symbols, sizes, hashes and alignment
are retained in Static.lean.in, so changed compiler output fails closed.
"""
import hashlib
import importlib.util
import pathlib
import struct
import sys

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[5]
GENERATED = ROOT / 'SSA/Projects/Agave/Ed25519/MLIR/generated'
spec = importlib.util.spec_from_file_location(
    'byte_globals', ROOT / 'SSA/Projects/RIR/Tools/extract_byte_globals.py')
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

serial = mod.extract((GENERATED / 'agave_serial_double_base.mlir').read_text(), [
    'alloc_eaf951945d20f8425ce4c25607db196f'])[0]
avx2 = mod.extract((GENERATED / 'agave_avx2_double_base.mlir').read_text(), [
    '_RNvNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx29constants26BASEPOINT_ODD_LOOKUP_TABLE'
])[0]
template = (HERE / 'Static.lean.in').read_text()
for record in [serial, avx2]:
    assert record['symbol'] in template
    assert record['sha256'] in template
sb = bytes.fromhex(serial['bytes_hex'])
ab = bytes.fromhex(avx2['bytes_hex'])
assert serial['length'] == 7680 and serial['alignment'] == 8
assert avx2['length'] == 10240 and avx2['alignment'] == 32
assert hashlib.sha256(sb).hexdigest() == serial['sha256']
assert hashlib.sha256(ab).hexdigest() == avx2['sha256']
sw = struct.unpack('<960Q', sb)
aw = struct.unpack('<2560I', ab)
p = 2**255 - 19
d = (-121665 * pow(121666, -1, p)) % p
points, factors = [], []
for k in range(64):
    sc = [sum(sw[15*k+5*c+i] * 2**(51*i) for i in range(5)) % p for c in range(3)]
    x = (sc[0] - sc[1]) * pow(2, -1, p) % p
    y = (sc[0] + sc[1]) * pow(2, -1, p) % p
    assert sc[2] == 2*d*x*y % p
    points.append((x, y, 1, x*y % p))
    ac = [sum((aw[40*k+8*i+lo] + 2**26 * aw[40*k+8*i+hi]) * 2**(51*i)
              for i in range(5)) % p for lo, hi in [(0, 2), (1, 3), (4, 6), (5, 7)]]
    f = ac[2] * pow(2*121666, -1, p) % p
    assert f != 0
    assert ac == [121666*f*(y-x) % p, 121666*f*(y+x) % p,
                  2*121666*f % p, -2*121665*f*x*y % p]
    factors.append(f)

replacements = {
    '@@SERIAL_BITS@@': '0x' + sb[::-1].hex(),
    '@@AVX2_BITS@@': '0x' + ab[::-1].hex(),
    '@@SERIAL_POINTS@@': '![' + ',\n    '.join(
        '⟨' + ', '.join(map(str, point)) + '⟩' for point in points) + ']',
    '@@AVX2_SCALES@@': '![' + ',\n    '.join(map(str, factors)) + ']',
}
for old, new in replacements.items():
    assert template.count(old) == 1
    template = template.replace(old, new)
if '--check' in sys.argv:
    assert (HERE / 'Static.lean').read_text() == template, 'Generated certificate differs'
else:
    (HERE / 'Static.lean').write_text(template)
print('Static table certificate matches extracted globals')

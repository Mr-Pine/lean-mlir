#!/usr/bin/env python3
"""Extract explicitly requested, relocation-free constant byte globals from generic MLIR.

Fail closed: mutable globals, nonzero address spaces, relocation regions, absent initializers,
non-byte types, and malformed sizes/alignment are rejected. This is an audited extraction step,
not a theorem about LLVM's frontend. ByteGlobal.Present supplies its exact memory contract.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path


STRING = r'"((?:[^"\\]|\\.)*)"'


def decode_string(raw: str) -> bytes:
    out = bytearray()
    i = 0
    while i < len(raw):
        if raw[i] != '\\':
            if ord(raw[i]) > 127:
                raise ValueError('non-ASCII literal in byte initializer')
            out.append(ord(raw[i]))
            i += 1
        elif i + 2 < len(raw) and re.fullmatch('[0-9A-Fa-f]{2}', raw[i + 1:i + 3]):
            out.append(int(raw[i + 1:i + 3], 16))
            i += 3
        elif i + 1 < len(raw) and raw[i + 1] in '\\"':
            out.append(ord(raw[i + 1]))
            i += 2
        else:
            raise ValueError(f'unsupported string escape at character {i}')
    return bytes(out)


def extract(text: str, symbols: list[str]) -> list[dict]:
    if len(symbols) != len(set(symbols)):
        raise ValueError('duplicate requested symbol')
    lines = text.splitlines()
    found = {}
    for i, line in enumerate(lines):
        if not line.lstrip().startswith('"llvm.mlir.global"()'):
            continue
        name = re.search(r'\bsym_name\s*=\s*' + STRING, line)
        if not name or name[1] not in symbols:
            continue
        name = name[1]
        if name in found:
            raise ValueError(f'duplicate definition of {name}')
        if not re.search(r'(?:[{,]\s*)constant\s*[,}]', line):
            raise ValueError(f'{name}: mutable or not explicitly constant')
        if not re.search(r'\baddr_space\s*=\s*0\s*:\s*i32\b', line):
            raise ValueError(f'{name}: unsupported address space')
        ty = re.search(r'\bglobal_type\s*=\s*!llvm.array<(\d+)\s*x\s*i8>', line)
        if not ty:
            raise ValueError(f'{name}: only relocation-free byte arrays are supported')
        n = int(ty[1])
        align = re.search(r'\balignment\s*=\s*(\d+)\s*:\s*i64', line)
        if not align or (a := int(align[1])) <= 0 or a & (a - 1):
            raise ValueError(f'{name}: expected explicit power-of-two alignment')
        # Constant value attributes must have an empty initializer region.
        if i + 1 >= len(lines) or lines[i + 1].strip() != '}) : () -> ()':
            raise ValueError(f'{name}: initializer regions/relocations are unsupported')
        string = re.search(r'\bvalue\s*=\s*' + STRING, line)
        dense = re.search(r'\bvalue\s*=\s*dense<(-?\d+)>\s*:\s*tensor<(\d+)xi8>', line)
        if string:
            data = decode_string(string[1])
        elif dense:
            if int(dense[2]) != n or not -128 <= int(dense[1]) <= 255:
                raise ValueError(f'{name}: invalid dense i8 initializer')
            data = bytes([int(dense[1]) % 256]) * n
        else:
            raise ValueError(f'{name}: missing or unsupported initializer')
        if len(data) != n:
            raise ValueError(f'{name}: initializer has {len(data)} bytes; type has {n}')
        found[name] = dict(symbol=name, length=n, alignment=a, bytes_hex=data.hex(),
                           sha256=hashlib.sha256(data).hexdigest())
    missing = set(symbols) - found.keys()
    if missing:
        raise ValueError(f'missing global definitions: {sorted(missing)}')
    return [found[symbol] for symbol in symbols]


def lean(records: list[dict]) -> str:
    lines = ['module', '', 'public import SSA.Projects.RIR.Global', '',
             'namespace LeanMLIR.RIR.ExtractedGlobals', '', '@[expose] public section', '']
    for i, g in enumerate(records):
        # A hexadecimal numeral avoids any ambiguity about MLIR escaping or byte order.
        bits = '0x' + (bytes.fromhex(g['bytes_hex'])[::-1].hex() or '0')
        name = json.dumps(g['symbol'])
        lines += [f'-- Source bytes SHA-256: {g["sha256"]}',
                  f'def global{i} : ByteGlobal :=',
                  f'  ⟨{name}, {g["length"]}, {bits}, {g["alignment"]}, by decide⟩', '']
    return '\n'.join(lines + ['end', 'end LeanMLIR.RIR.ExtractedGlobals', ''])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('symbols', nargs='+')
    parser.add_argument('--lean', type=Path)
    parser.add_argument('--manifest', type=Path)
    args = parser.parse_args()
    records = extract(args.input.read_text(), args.symbols)
    if args.lean:
        args.lean.write_text(lean(records))
    output = json.dumps(records, indent=2) + '\n'
    if args.manifest:
        args.manifest.write_text(output)
    else:
        print(output, end='')


if __name__ == '__main__':
    main()

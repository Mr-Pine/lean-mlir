"""Lift Firedancer functions to RIR `mlir_def`s.

    python3 lift.py --src <build>/mlir_canonicalized --impl ref --out <Lib>/Ref/Mlir \
        --prefix <Lib>.Ref.Mlir --ns MLIR.<Lib>.Ref fd_ed25519_verify

writes `<out>/<f>.lean` for each `f` and every function and global it reaches, from
`<src>/<impl>/region/<f>.mlir`. Each file quotes its
region verbatim, binds every callee and global (`with @f := f`), and is `noncomputable` when it
reaches a table too long for the code generator.
"""
import argparse, os, re

ap = argparse.ArgumentParser()
ap.add_argument('--impl', required=True, choices=['ref', 'avx512'])
ap.add_argument('--out', required=True)
ap.add_argument('--prefix', required=True, help='module prefix of the lifts')
ap.add_argument('--ns', required=True, help='namespace of the lifts')
ap.add_argument('--src', required=True, help='the `mlir_canonicalized` directory')
ap.add_argument('funcs', nargs='+')
args = ap.parse_args()
SRC = os.path.join(os.path.expanduser(args.src), args.impl, 'region')

def region(f):
    return open(f'{SRC}/{f}.mlir').read().rstrip('\n')

def deps(f):
    s = region(f)
    calls = sorted(set(re.findall(r'callee = @([A-Za-z_0-9.]+)', s)))
    globs = sorted(set(re.findall(r'global_name = @([A-Za-z_0-9.]+)', s)))
    return calls, globs

def lean(f):
    """`f`'s Lean name: a symbol's dots would make it a namespace."""
    return f.replace('.', '_')

def big(f):
    """A table too long for the code generator."""
    return '^bb' not in region(f) and len(region(f)) > 20000

def nc(f):
    """A big table, or a lift reaching one: noncomputable."""
    calls, globs = deps(f)
    return big(f) or any(nc(d) for d in calls + globs)

def with_lines(binds):
    """`with @f := f, …`, wrapped at 100 columns."""
    if not binds:
        return []
    out, cur = [], '  with'
    for i, b in enumerate(binds):
        item = ' ' + b + (',' if i + 1 < len(binds) else '')
        if len(cur) + len(item) > 100:
            out.append(cur)
            cur = '   '
        cur += item
    return out + [cur]

def write(f, seen):
    if f in seen:
        return
    seen.add(f)
    calls, globs = deps(f)
    for d in calls + globs:
        write(d, seen)
    glob = '^bb' not in region(f)
    base = 'GlobalInitializer' if glob else 'Func'
    imps = [f'{args.prefix}.{lean(d)}' for d in calls + globs]
    binds = [f'@{d} := {lean(d)}' for d in calls + globs]
    cmd = ('noncomputable ' if nc(f) else '') + ('mlir_const_def' if glob else 'mlir_def')
    lines = ['module', '',
             f'-- build/native/gcc/mlir_canonicalized/{args.impl}/region/{f}.mlir', '',
             f'public import MLIR.Semantics.{base}',
             'public import MLIR.Syntax.Elab']
    lines += [f'public import {i}' for i in imps]
    lines += ['', f'meta import MLIR.Semantics.{base}']
    lines += [f'meta import {i}' for i in imps]
    lines += ['', f'namespace {args.ns}', '', '@[expose] public section', '',
              f'{cmd} {lean(f)} :=', region(f)] + with_lines(binds)
    lines += ['', 'end', '', f'end {args.ns}', '']
    os.makedirs(args.out, exist_ok=True)
    open(os.path.join(args.out, f'{lean(f)}.lean'), 'w').write('\n'.join(lines))
    print(f)

seen = set()
for f in args.funcs:
    write(f, seen)

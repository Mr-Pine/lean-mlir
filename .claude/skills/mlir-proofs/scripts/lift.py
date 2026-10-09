"""Lift Firedancer functions to RIR `mlir_def`s.

    python3 lift.py --src <build>/mlir_canonicalized --impl ref --out <Lib>/Ref/Mlir \
        --prefix <Lib>.Ref.Mlir --ns MLIR.<Lib>.Ref fd_ed25519_verify

writes `<out>/<f>.lean` for each `f` and every function and global it reaches, from
`<src>/<impl>/op/<f>.mlir`. Each file quotes its `"llvm.func"` or `"llvm.mlir.global"` op
verbatim, binds every callee and global (`with @f := f`), and is `noncomputable` when it
reaches a table too long for the code generator.

With `--share-from ref --share-prefix <Lib>.Ref.Mlir --share-ns Ref`, a function whose op equals
the other implementation's up to SSA numbering and the target attributes (`target_cpu`,
`target_features`, `tune_cpu`, which have no IR semantics) is bound to that lift instead;
`--share-src` compares against another extraction's ops (another checkout or profile).
`--header` names the op directory in each lift's first comment line when it is not `build/…`
of the main checkout. A callee without an op file (an external declaration, e.g. assembly) is
bound to the `Func` of its name in `--extern-prefix`'s module of that name, written by hand (its
callers are `noncomputable`, as an axiomatized body is).
"""
import argparse, os, re

ap = argparse.ArgumentParser()
ap.add_argument('--impl', required=True, choices=['ref', 'avx512'])
ap.add_argument('--out', required=True)
ap.add_argument('--prefix', required=True, help='module prefix of the lifts')
ap.add_argument('--ns', required=True, help='namespace of the lifts')
ap.add_argument('--src', required=True, help='the `mlir_canonicalized` directory')
ap.add_argument('--header', help='the op directory as lift headers name it (default: from build/ on)')
ap.add_argument('--share-src', help='the `mlir_canonicalized` directory to share from (default: --src)')
ap.add_argument('--share-from', choices=['ref', 'avx512'])
ap.add_argument('--share-prefix')
ap.add_argument('--share-ns')
ap.add_argument('--extern-prefix', help='module prefix of the `Func`s for external callees')
ap.add_argument('funcs', nargs='+')
args = ap.parse_args()

def external(f):
    """A callee with no body here: an external declaration (assembly, say)."""
    return not os.path.exists(f'{SRC}/{f}.mlir')
SRC = os.path.join(os.path.expanduser(args.src), args.impl, 'op')
# the header names the op file from the build directory on, as the lifts quote it
HDR = args.header or (SRC[SRC.index('build/'):] if 'build/' in SRC else SRC)

def region(f, src=None):
    return open(f'{src or SRC}/{f}.mlir').read().rstrip('\n')

TARGET = re.compile(r', (target_cpu = "[^"]*"|tune_cpu = "[^"]*"|'
                    r'target_features = #llvm.target_features<\[[^\]]*\]>)|'
                    r', \["(target-cpu|tune-cpu|target-features)", "[^"]*"\]')

def shared(f):
    """`f`'s op is the other implementation's, up to numbering and target attributes."""
    if not args.share_from:
        return False
    other = os.path.join(os.path.expanduser(args.share_src or args.src), args.share_from, 'op')
    if not os.path.exists(f'{other}/{f}.mlir'):
        return False
    norm = lambda t: TARGET.sub('', re.sub(r'%(?:arg)?\d+\b', '%', t))
    return norm(region(f)) == norm(region(f, other))

def deps(f):
    s = region(f)
    calls = sorted(set(re.findall(r'callee = @([A-Za-z_0-9.]+)', s)))
    globs = sorted(set(re.findall(r'global_name = @([A-Za-z_0-9.]+)', s)))
    return calls, globs

def lean(f):
    """`f`'s Lean name: a symbol's dots would make it a namespace."""
    return f.replace('.', '_')

def is_global(f):
    return '"llvm.mlir.global"()' in region(f).split('({', 1)[0]

def big(f):
    """A table too long for the code generator."""
    return is_global(f) and len(region(f)) > 20000

def nc(f):
    """A big table, or a lift reaching one: noncomputable."""
    calls, globs = deps(f)
    return big(f) or any(external(d) or nc(d) for d in calls + globs)

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
        if not shared(d) and not external(d):
            write(d, seen)
    glob = is_global(f)
    base = 'GlobalInitializer' if glob else 'Func'
    def prefix(d):
        if external(d):
            if not args.extern_prefix:
                raise SystemExit(f'{f} calls external {d}: pass --extern-prefix')
            return args.extern_prefix
        return args.share_prefix if shared(d) else args.prefix
    imps = [f'{prefix(d)}.{lean(d)}' for d in calls + globs]
    binds = [f'@{d} := {args.share_ns + "." if shared(d) else ""}{lean(d)}' for d in calls + globs]
    cmd = ('noncomputable ' if nc(f) else '') + ('mlir_const_def' if glob else 'mlir_def')
    lines = ['module', '',
             f'-- {HDR}/{f}.mlir', '',
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

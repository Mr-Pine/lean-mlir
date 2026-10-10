"""Lift Firedancer functions to RIR `mlir_def`s.

    python3 lift.py --src <build>/mlir_canonicalized --impl ref --out <Lib>/Ref/Mlir \
        --prefix <Lib>.Ref.Mlir --ns MLIR.<Lib>.Ref fd_ed25519_verify

writes `<out>/<f>.lean` for each `f` and every function and global it reaches, from
`<src>/<impl>/op/<f>.mlir`. Each file quotes its `"llvm.func"` or `"llvm.mlir.global"` op
verbatim, binds every callee and global (`with @f := f`), and is `noncomputable` when it
reaches a table or a function too long for the code generator.

With `--share-from ref --share-prefix <Lib>.Ref.Mlir --share-ns Ref`, a function whose op equals
the other implementation's up to SSA numbering and the target attributes (`target_cpu`,
`target_features`, `tune_cpu`, which have no IR semantics) is bound to that lift instead;
`--share-src` compares against another extraction's ops (another checkout or profile).
`--header` names the op directory in each lift's first comment line when it is not `build/…`
of the main checkout. A callee without an op file (an external declaration, e.g. assembly) is
bound to the `Func` of its name in `--extern-prefix`'s module of that name, written by hand (its
callers are `noncomputable`, as an axiomatized body is). Calls the translation models need no
binding: external library functions `LIBFUNCS`, and calls marked `noreturn` (UB).

`--ops <dir>` lifts from an op directory directly (instead of `--src`/`--impl`), and `--all` lifts
every function and global in it. Mangled C++ and Rust symbols (`_Z…`, `_R…`) get readable Lean
names: `c++filt`'s demangling, shortened to the item and its type or trait, made unique over the
directory's symbols in sorted order; such a lift's second comment line is the demangled symbol.
"""
import argparse, os, re, subprocess

ap = argparse.ArgumentParser()
ap.add_argument('--impl', choices=['ref', 'avx512'])
ap.add_argument('--out', required=True)
ap.add_argument('--prefix', required=True, help='module prefix of the lifts')
ap.add_argument('--ns', required=True, help='namespace of the lifts')
ap.add_argument('--src', help='the `mlir_canonicalized` directory')
ap.add_argument('--ops', help='the op directory itself, instead of `--src` and `--impl`')
ap.add_argument('--all', action='store_true', help='lift every function and global')
ap.add_argument('--header', help='the op directory as lift headers name it (default: from build/ on)')
ap.add_argument('--share-src', help='the `mlir_canonicalized` directory to share from (default: --src)')
ap.add_argument('--share-from', choices=['ref', 'avx512'])
ap.add_argument('--share-prefix')
ap.add_argument('--share-ns')
ap.add_argument('--extern-prefix', help='module prefix of the `Func`s for external callees')
ap.add_argument('funcs', nargs='*')
args = ap.parse_args()
if not args.ops and not (args.src and args.impl):
    raise SystemExit('pass --ops, or --src and --impl')

def external(f):
    """A callee with no body here: an external declaration (assembly, say)."""
    return not os.path.exists(f'{SRC}/{f}.mlir')
SRC = os.path.expanduser(args.ops) if args.ops else os.path.join(os.path.expanduser(args.src), args.impl, 'op')
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

# library functions the translation models when unbound (`libCall?` in Translate.lean)
LIBFUNCS = {'bcmp', 'memcmp', 'explicit_bzero', '__explicit_bzero_chk', 'memset_explicit'}

def deps(f):
    """The symbols `f` calls and addresses, less the calls the translation models. A global's
    initializer binds nothing: its addresses are of pointers the translation leaves undefined."""
    if is_global(f):
        return [], []
    s = region(f)
    calls = set()
    for line in s.splitlines():
        m = re.search(r'callee = @([A-Za-z_0-9.]+)', line)
        if m and not (m.group(1) in LIBFUNCS and external(m.group(1))) \
                and not re.search(r'[{,] noreturn[,}]', line):
            calls.add(m.group(1))
    globs = sorted(set(re.findall(r'global_name = @([A-Za-z_0-9.]+)', s)))
    return sorted(calls), globs

KEYWORDS = {'at', 'by', 'do', 'else', 'end', 'fun', 'from', 'have', 'if', 'in', 'let', 'match',
            'open', 'show', 'then', 'where', 'with', 'def', 'theorem', 'section', 'namespace'}

def ident(s):
    return re.sub(r'\W+', '_', s).strip('_')

def split_top(s, sep):
    """`s` split at `sep` outside `<…>`, `(…)` and `[…]`."""
    out, depth, cur, i = [], 0, '', 0
    while i < len(s):
        if depth == 0 and s.startswith(sep, i):
            out.append(cur)
            cur, i = '', i + len(sep)
            continue
        c = s[i]
        depth += c in '<([' and 1 or 0
        depth -= c in '>)]' and 1 or 0
        cur += c
        i += 1
    return out + [cur]

def rust_type(t):
    """The name components of a Rust type: its last path segment and generic arguments."""
    t = t.strip().lstrip('&').strip()
    if t.startswith('mut '):
        t = t[4:]
    if t.startswith('[') and t.endswith(']'):
        return ['slice'] + rust_type(t[1:-1])
    return rust_path(t)

def rust_path(p, last=True):
    """The name components of a demangled Rust path: a qualified `<T as Tr>::m…` keeps every
    segment, a plain one only its last (`last`), each with its generic arguments."""
    segs = [x.strip() for x in split_top(p.strip(), '::')]
    comps = []
    if segs[0].startswith('<'):
        qs = split_top(segs[0][1:-1], ' as ')
        comps += rust_type(qs[0])
        if len(qs) > 1:
            comps += rust_path(qs[1])
        segs, last = segs[1:], False
    # a turbofish `::<…>` belongs to the segment before it
    groups = []
    for seg in segs:
        if seg.startswith('<') and groups:
            groups[-1] += seg
        else:
            groups.append(seg)
    for g in groups[-1:] if last else groups:
        name, _, gen = g.partition('<')
        if name and not re.fullmatch(r'__Impl_\w*__', name):
            comps.append(name)
        if gen:
            for a in split_top(gen[:-1], ','):
                comps += rust_type(a)
    return comps

def readable(demangled):
    """A demangled symbol's short name components, and its C++ parameters' (for overloads)."""
    d = re.sub(r'\[[0-9a-f]+\]', '', demangled)
    if '(' in d and not d.startswith('<'):
        # C++: `ns::f(params)`, or a local `ns::f(params)::x`
        head, _, rest = d.partition('(')
        params, _, tail = rest.rpartition(')')
        comps = [head.split('::')[-1]] + [c for c in tail.split('::') if c.strip()]
        ps = [ident(re.sub(r'\b(const|unsigned|signed|struct)\b|[*&]', '', q).split('::')[-1])
              for q in split_top(params, ',')]
        return comps, [q for q in ps if q]
    return rust_path(d), []

def names(syms):
    """Lean names for `syms`, unique: demangled ones shortened, their C++ parameters or an index
    appended on a clash, in sorted order."""
    mangled = sorted(s for s in syms if re.match(r'_(Z|R)', s))
    out = subprocess.run(['c++filt'], input='\n'.join(mangled), capture_output=True, text=True,
                         check=True).stdout.split('\n') if mangled else []
    demangled = dict(zip(mangled, out))
    base = {}
    for s in sorted(syms):
        if s in demangled and demangled[s] != s:
            comps, params = readable(demangled[s])
            dedup = [c for k, c in enumerate(comps) if k == 0 or c != comps[k - 1]]
            base[s] = (ident('_'.join(ident(c) for c in dedup)), params)
        else:
            base[s] = (s.replace('.', '_'), [])
    result, used = {}, set()
    for s in sorted(syms):
        b, params = base[s]
        clash = sum(1 for t in syms if base[t][0] == b) > 1
        n = '_'.join([b] + params) if clash and params else b
        if n in KEYWORDS or n[0].isdigit():
            n += '_'
        k, m = 1, n
        while m in used:
            k += 1
            m = f'{n}_{k}'
        used.add(m)
        result[s] = m
    return result, demangled

def all_syms():
    here = [f[:-5] for f in os.listdir(SRC) if f.endswith('.mlir')]
    ext = set()
    for f in here:
        c, _ = deps(f)
        ext |= {d for d in c if external(d)}
    return here + sorted(ext)

def lean(f):
    """`f`'s Lean name: demangled, and without dots, which would make it a namespace."""
    return NAMES.get(f) or f.replace('.', '_')

def is_global(f):
    return '"llvm.mlir.global"()' in region(f).split('({', 1)[0]

def big(f):
    """A table, or a function of more values (a register context), too long for the code
    generator."""
    if is_global(f):
        return len(region(f)) > 20000
    return len(re.findall(r'^\s*%\d+(?:, %\d+)* = |^\^\w+\(', region(f), re.M)) > 2000

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
    dm = [f'-- {DEMANGLED[f]}'] if DEMANGLED.get(f, f) != f else []
    lines = ['module', '',
             f'-- {HDR}/{f}.mlir'] + dm + ['',
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

NAMES, DEMANGLED = names(all_syms())
seen = set()
funcs = sorted(f[:-5] for f in os.listdir(SRC) if f.endswith('.mlir')) if args.all else args.funcs
for f in funcs:
    write(f, seen)

"""Lift LLVM functions to RIR `mlir_def`s.

    python3 lift.py --src <build>/mlir_canonicalized --impl ref --out <Lib>/Ref/Mlir \
        --prefix <Lib>.Ref.Mlir --ns MLIR.<Lib>.Ref fd_ed25519_verify

writes `<out>/<f>.lean` for each `f` and every function and global it reaches, from
`<src>/<impl>/op/<f>.mlir`. Each file quotes its `"llvm.func"` or `"llvm.mlir.global"` op
verbatim, binds every callee and global (`with @f := f`), and is `noncomputable` when it
reaches a table or a function too long for the code generator.

With `--share-from ref --share-prefix <Lib>.Ref.Mlir --share-ns Ref`, a function whose op equals
one of the other implementation's is bound to that lift instead (and `--all` skips it); the other
is the function of the same symbol or Lean name, else any whose op equals. Ops are compared up to
SSA numbering, symbol names (callees as bound), TBAA (alias definitions and access tags), and the
function attributes and `passthrough` entries `Translate.funcAttrUses`/`passthroughUses` mark
inert or ignored (target, calling convention, linkage, memory effects, `warn-stack-size`, …): the
translation reads none of them. `--share-src` compares against another extraction's ops (another
checkout or profile), `--share-ops <dir>` against an op directory itself (another project's,
`--share-ns` then its full namespace).
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
ap.add_argument('--share-ops', help='the op directory to share from, instead of --share-from')
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

# `Translate.funcAttrUses`' inert and ignored function attributes, `passthroughUses`' entries
INERT = {'CConv', 'linkage', 'visibility_', 'dso_local', 'unnamed_addr', 'no_inline', 'inline_hint',
         'minsize', 'optsize', 'uwtable_kind', 'frame_pointer', 'personality', 'target_cpu',
         'target_features', 'tune_cpu', 'memory_effects', 'will_return', 'no_unwind', 'sym_name'}
PASS = {'mustprogress', 'willreturn', 'nofree', 'norecurse', 'nosync', 'nocallback',
        'min-legal-vector-width', 'no-trapping-math', 'ssp', 'sspstrong',
        'stack-protector-buffer-size', 'probe-stack', 'nonlazybind', 'warn-stack-size',
        'target-cpu', 'target-features', 'tune-cpu'}

def split_attrs(s):
    """`s` split at each `, ` outside brackets and strings."""
    out, depth, cur, q, i = [], 0, '', False, 0
    while i < len(s):
        c = s[i]
        if c == '"' and (i == 0 or s[i - 1] != '\\'):
            q = not q
        elif not q and c in '<([{':
            depth += 1
        elif not q and c in '>)]}' and s[i - 1] != '-':
            depth -= 1
        elif not q and depth == 0 and s.startswith(', ', i):
            out, cur, i = out + [cur], '', i + 2
            continue
        cur += c
        i += 1
    return out + [cur]

def norm_head(h):
    """A function's header without the attributes the translation does not read."""
    m = re.match(r'(.*?"llvm.func"\(\) <\{)(.*)(\}> \(\{)$', h, re.S)
    if not m:
        return h
    keep = []
    for a in split_attrs(m.group(2)):
        k = a.split(' = ', 1)[0]
        if k == 'passthrough':
            ps = [p for p in split_attrs(a.split(' = ', 1)[1][1:-1])
                  if (p[2:].split('"')[0] if p.startswith('[') else p.strip('"')) not in PASS]
            a = f'passthrough = [{", ".join(ps)}]'
        if k not in INERT:
            keep.append(a)
    return m.group(1) + ', '.join(keep) + m.group(3)

def norm(t, sym=lambda d: d):
    """`t` up to SSA numbering, TBAA, symbol names (each `@d` as `sym(d)`) and, for a function,
    the attributes the translation does not read."""
    t = '\n'.join(l for l in t.splitlines() if not re.match(r'#tbaa\w* = #llvm\.tbaa_', l))
    t = re.sub(r', tbaa = \[[^\]]*\]|tbaa = \[[^\]]*\], ', '', t)
    t = re.sub(r'%(?:arg)?\d+\b', '%', t)
    t = re.sub(r'((?:callee|global_name) = )@([A-Za-z_0-9.]+)', lambda m: m[1] + '@' + sym(m[2]), t)
    t = re.sub(r'sym_name = "[^"]*"', 'sym_name', t)
    head, sep, body = t.partition('({\n')
    return norm_head(head + '({') + '\n' + body if sep else t

def other_dir():
    if args.share_ops:
        return os.path.expanduser(args.share_ops)
    return os.path.join(os.path.expanduser(args.share_src or args.src), args.share_from, 'op')

SHARED = {}

def shared(f):
    """The other directory's function (or global) whose op is `f`'s up to `norm`, if any."""
    if not (args.share_from or args.share_ops) or external(f):
        return None
    if f not in SHARED:
        SHARED[f] = None
        mine = norm(region(f), lambda d: shared(d) or '!' + d)
        cands = [g for g in [f] + [g for g, n in OTHER_NAMES.items() if n == lean(f)]
                 if g in OTHER_OPS] + sorted(OTHER_OPS)
        SHARED[f] = next((g for g in cands if OTHER_OPS[g] == mine), None)
    return SHARED[f]

# library functions the translation models when unbound (`libCall?` in Translate.lean)
LIBFUNCS = {'bcmp', 'memcmp', 'explicit_bzero', '__explicit_bzero_chk', 'memset_explicit'}

def deps(f, src=None):
    """The symbols `f` calls and addresses, less the calls the translation models. A global's
    initializer binds nothing: its addresses are of pointers the translation leaves undefined."""
    if is_global(f, src):
        return [], []
    s = region(f, src)
    calls = set()
    for line in s.splitlines():
        m = re.search(r'callee = @([A-Za-z_0-9.]+)', line)
        lib = m and m[1] in LIBFUNCS and not os.path.exists(f'{src or SRC}/{m[1]}.mlir')
        if m and not lib and not re.search(r'[{,] noreturn[,}]', line):
            calls.add(m[1])
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

def all_syms(src=None):
    src = src or SRC
    here = [f[:-5] for f in os.listdir(src) if f.endswith('.mlir')]
    ext = set()
    for f in here:
        c, _ = deps(f, src)
        ext |= {d for d in c if not os.path.exists(f'{src}/{d}.mlir')}
    return here + sorted(ext)

def lean(f):
    """`f`'s Lean name: demangled, and without dots, which would make it a namespace."""
    return NAMES.get(f) or f.replace('.', '_')

def is_global(f, src=None):
    return '"llvm.mlir.global"()' in region(f, src).split('({', 1)[0]

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
    name = lambda d: OTHER_NAMES[shared(d)] if shared(d) else lean(d)
    imps = [f'{prefix(d)}.{name(d)}' for d in calls + globs]
    binds = [f'@{d} := {args.share_ns + "." if shared(d) else ""}{name(d)}' for d in calls + globs]
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
if args.share_from or args.share_ops:
    OTHER_NAMES = names(all_syms(other_dir()))[0]
    OTHER_OPS = {g: norm(region(g, other_dir())) for g in OTHER_NAMES
                 if os.path.exists(f'{other_dir()}/{g}.mlir')}
seen = set()
funcs = sorted(f[:-5] for f in os.listdir(SRC) if f.endswith('.mlir') and not shared(f[:-5])) \
    if args.all else args.funcs
for f in funcs:
    write(f, seen)

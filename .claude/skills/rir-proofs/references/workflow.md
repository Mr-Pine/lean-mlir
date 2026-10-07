# Workflow: from a C function to a proof

## 0. The project

A proof project is a lake package that requires this repository (package `MLIR`) by path, with one
`lean_lib` whose `globs` cover every module (`["<Lib>.+"]`), the same `lean-toolchain`, and
a manifest copied from an existing proof project (the package name in `«…»`). RIR imports no
Mathlib. A project that needs Mathlib for mathematical meaning sets `packagesDir` to this
repository's `.lake/packages`, where Mathlib is built; otherwise `lake` builds it from scratch.
Probe files go in a git-ignored directory outside the globs.

## 1. Choose the function and its call tree

Each implementation is its own tree (`Ref/`, `Avx512/`); never mix their lifts. List the callees
from the region (`grep -o 'callee = @[a-z_0-9.]*' f.mlir`) and prove bottom-up. Read the C source
next to the region: the spec mirrors the C, the proof follows the region.

## 2. Lift

`scripts/lift.py` (in this skill) writes `Mlir/<g>.lean` for a function and everything it reaches:

```bash
python3 lift.py --src <build>/mlir_canonicalized --impl ref --out <Lib>/Ref/Mlir \
  --prefix <Lib>.Ref.Mlir --ns MLIR.<Lib>.Ref fd_ed25519_verify
```

A lift is: `module`, the region's path (relative to the build directory) as the first comment,
imports (`public` and `meta` of the callees' lifts), the namespace, and
`mlir_def g := { region verbatim } with @callee := callee, @global := global`. No docstrings, no
other prose. The elaborator requires:

- a `with @f := t` binding for every called or addressed symbol; `t` is a lifted `Func`, a
  `GlobalInitializer`, or a parameter of the definition (`mlir_def g (cb : CB) := … with @f := cb`);
- `noncomputable` on a table too long for the code generator and on every lift that reaches it.

Build the lifts before opening proofs that import them. Never copy lifts from another project:
lift from the canonicalized regions, which each lift's first line names.

## 3. Spec and tests

Write the bv-level spec (`specs.md`) in the proof file, then test it against the lift in a
separate module (`Tests/<f>.lean`, importing the proof file), so the proofs never evaluate them:

```lean
#guard match fd_f25519_add.eval 1 (fd_f25519_add.args (.value r) (.value a) (.value b))
    (state aBytes bBytes) with
  | .value (some (.cons ret .nil), s') =>
    let s := state aBytes bBytes
    ret == .value r && (List.finRange 5).all fun k =>
      s'.mem.readLimbs r k == fd_f25519_add.spec (s.mem.readLimbs a) (s.mem.readLimbs b) k
  | _ => false
```

The fuel of `f.eval fuel` counts block jumps (a loop of `n` iterations needs `n + 2` or so), not
calls; out of fuel it returns `.value (none, _)`.

A failing test is a wrong spec, or a wrong layout assumption (the Edwards struct is X, Y, T, Z at
offsets 0, 40, 80, 120), found in seconds instead of in a stuck proof. A `noncomputable` lift
cannot be evaluated; test its spec on the parts that can.

A spec's limbs are functions, recomputed at every use: an expected value nested a few calls deep
takes minutes. Compute it with each callee's result memoized, `(Vector.ofFn l).get` per limb
function (a `let v := …; fun i => v[i]` did not memoize in practice).

## 4. The `call_eq` theorem

State it (`specs.md`), then prove it with the steps (`tactics-guide.md`):

1. write `sorry` after `func_init; block_init` and look at the context with `lean_goal`;
2. step through, checking every few steps; name the C variables; keep the state clean
   (`SKILL.md`);
3. at a branch, finish one target before the next (`case isTrue => …`);
4. loops: state and prove the loop lemma first (`patterns.md`, P7/P8), then `step_loop` it;
5. close the final equation; `lean_verify` the theorem.

## 5. Mathematical meaning

When a caller or the final theorem needs it, prove what the spec means (`specs.md`) in a module
the bv-level proofs do not import.

## 6. Check and commit

- `lean_diagnostic_messages` on the whole file, no severity filter: no errors, no `sorry`, no
  warnings.
- `lean_verify` on each public theorem.
- Format with `lean-fmt` (the build for the project's toolchain; it needs the modules built).
  It can garble tactic quotations (`have $x := e` to `have $x :=e`): check
  `grep -n ':=[A-Za-z(]'` afterwards, and leave a file it breaks unformatted.
- `lake build` of the project once, stopped at the first error.
- Re-read every docstring and comment, then commit: one function per commit, short subject.

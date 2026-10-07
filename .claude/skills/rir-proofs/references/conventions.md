# Conventions

## File layout

```
<Lib>/
  <Impl>/                one tree per implementation (Ref, Avx512)
    Mlir/<f>.lean        lifts, generated (workflow.md §2)
    <f>.lean             f.spec, lemmas, f.call_eq
    Tests/<f>.lean       #guard tests of f.spec against the lift
  Common/                what the implementations share: object predicates, read/store
                         functions, project tactics
  Math/                  mathematical meaning (may import Mathlib; nothing above imports it)
```

- One proof file per lifted function, named as the C function. Lemmas used by one function stay
  in its file; lemmas used by several move to `Common/` (or to the implementation's shared file)
  once the proofs using them work.
- Implementations never import each other's proofs; shared statements go to `Common/`.
- The project's own tactics (`name_limbs`, `clear_reads`) live in `Common/Tactics.lean`.

## A proof file

```lean
module

public import SSA.Projects.RIR.Run.Tactic
public import <Common modules>
public import <callees' proof files>
public import <the lift>

namespace LeanMLIR.RIR.<Lib>.<Impl>

/-! ## Specification -/
@[expose] public section
<f.spec and its helpers>
end

/-! ## Proof -/
section Proof
<proof macros, all before the first theorem>
<lemmas: overflow facts, branch lemmas, loop lemmas>
public theorem f.call_eq … := by …
end Proof

end LeanMLIR.RIR.<Lib>.<Impl>
```

Tests import the proof file and sit in `Tests/<f>.lean`.

## Names

| Thing | Name |
| --- | --- |
| lift | the C function's name (`fd_f25519_add`); a symbol's dots become `_` |
| spec function | `f.spec`; one per output object if the C computes them independently |
| main theorem | `f.call_eq` |
| loop lemma | `f.<what>_loop` (`fd_curve25519_scalar_wnaf.unpack_loop`), after the C loop's purpose |
| block / iteration lemma | `f.<what>_block`, `f.<what>_iter` |
| pattern | `fooRun` (the instructions), `runBodyFrom_fooRun` (the lemma) |
| header env | `abbrev f.hdr<k> … E i : ⟪f.Γ⟫` for the header `^bb<k>` |
| step values | the C variables (`with x6`); slots after the C locals |
| object predicate | `LimbsFit`, … (`Fit` for memory layout, `Bounded` for value ranges) |
| hypotheses | `h` + what: `hwf`, `hr` (for pointer `r`), `hsep` (separation), `hbr…` (branches) |

No project prefixes the namespace already gives (`rir_…`, `fd_…` on lemmas).

## Comments

- A docstring says what the declaration is or states, in one sentence, and at most one more on
  why; a declaration whose name says it needs none. No filler, no references to other projects
  or to where code was adapted from.
- `call_eq` docstrings: what is stored where, what is returned, what may alias.
- Step comments quote the C line a group of steps implements
  (`-- x6 = ((x1 & UINT64_C(0x7ffffffffffff)) + ((x5 >> 51) * UINT8_C(0x13)));`).
- Lifts carry no docstrings, only the region path.

## Commits

- One working function (its spec, proof, tests) per commit.
- Subject: short and precise, the repository's style; a body of at most two sentences when the
  diff does not say it.
- Format each file with `lean-fmt` inside the commit; never a separate formatting commit.
- Framework changes in their own commits on the framework's working branch, one change each.

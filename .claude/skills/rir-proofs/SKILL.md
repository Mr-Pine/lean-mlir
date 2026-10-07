---
name: rir-proofs
description: Proving lifted LLVM/MLIR functions in the register-based IR (RIR, MLIR) — lifting with mlir_def, bv-level specs, call_eq theorems, loop and callee lemmas, the step tactics, proof patterns, performance and conventions. Use for any proof about a function defined with mlir_def.
---

# RIR proofs

Proofs that a lifted function computes its specification: `f.call (f.args …) s = .value (rets, s')`,
stepped instruction by instruction with the RIR tactics. The framework lives in
`MLIR` (this repository); proof projects are separate lake packages that depend on
it by path.

| Reference | Contents |
| --- | --- |
| `references/workflow.md` | from a C function to a committed proof, step by step |
| `references/specs.md` | the bv-level spec style, statements, preconditions, mathematical meaning |
| `references/tactics.md` | every tactic: syntax, options, context, produced facts, failures |
| `references/tactics-guide.md` | the tactics in proof order, examples, common mistakes |
| `references/patterns.md` | proof patterns with worked examples |
| `references/performance.md` | profiling recipe and known slow patterns |
| `references/conventions.md` | naming, comments, file layout, commits |

## Working rules

1. **Check through the `lean-lsp` MCP tools**, never `lake env lean`:
   `lean_diagnostic_messages` with a line range for errors, `lean_goal` for states,
   `lean_multi_attempt` to try tactics without editing, `lean_profile_proof` for slow steps,
   `lean_verify` for the final axiom check.
2. **`lake build <module>` only** after editing a file others import (so the LSP sees the new
   `.olean`), and once before each commit. Stop at the first `error:`; keep Bash timeouts
   ≤ 300 s and run longer builds in the background.
3. **Scratch files** live in the project tree outside the library globs and never
   `import Mathlib`.
4. **Never run `lake` under `git rebase --exec`** or a git hook without unsetting every `GIT_*`
   variable first.
5. **Bottom-up**: a function's proof needs its callees' `call_eq`; prove leaves first, or take an
   unproved callee as a parameter with a spec hypothesis (`patterns.md`, P9).

## Decision tree: the next instruction

```
func_init / block_init done? ── no ──> func_init (once), block_init (each block)
│
next instruction (infoview "Instructions" panel)
├─ constant, arithmetic, icmp, select, gep, cast, vector op, lifetime.* → step_pure
│    └─ flagged op (nsw/nuw) or gep → no-overflow lemma as simp arg if the step leaves an `if`
├─ load → step_load            ├─ store → step_store
├─ memcpy / memset → step_memcpy / step_memset
├─ call @f → step_call using f.call_eq (or the callee hypothesis)
├─ alloca → step_alloca        ├─ addressof @g → step_addressof g.value_eq
├─ a run of instructions that recurs → step_pattern using <pattern lemma>
└─ end of body → finish_block
     ├─ return → close the final equation (tactics-guide §11)
     ├─ jump to a block not yet run → block_init, continue
     └─ jump to a loop header / shared block → step_loop using <lemma> (or the IH / hK)
```

## Rules

- No `sorry`; `lean_verify` shows only `propext`, `Classical.choice`, `Quot.sound`, and the
  `…_native.bv_decide.ax_…` axioms of `bv_decide` (allowed). No `native_decide`.
- `maxHeartbeats` only with a comment saying why the proof needs it; never `maxRecDepth`
  (bisect to the `fun ⟨…⟩`, `simpa` or unification on a big literal instead).
- No warnings: unused simp arguments, unused variables and every linter (Mathlib's included,
  e.g. `unnecessarySeqFocus`) are fixed, not silenced.
- No workaround that only hides a problem (a weakened spec, an unused hypothesis, a `try` that
  swallows a failing step).
- Case splits over `Fin n` use Mathlib's `fin_cases` (`import Mathlib.Tactic.FinCases` and
  `Mathlib.Data.Fintype.Basic`), never `split` on a `match` or `match i, hi with | 0, _ …`.
- Every `local macro` and `macro` a proof uses is defined before the file's first theorem.
- Name step values after the C source's variables (`with x6`); inline only what an overflow
  lemma must see expanded.
- In a step context (hundreds of hypotheses), never run a tactic that scans the whole context:
  `simp_all`, `simp … at *`, `bv_omega`, `omega` over BitVec goals. `decide` closes literal side
  goals.
- Shared lemmas go to the shared module only after the proof using them works (each edit there
  rebuilds every importer).
- `#guard` tests live in their own module (`Tests/<f>.lean`), never in a proof file.

## Keep the proof state clean

At every step `lean_goal` should read like the C code at that point: the live objects, their
facts, and `hS` as a short chain of named writes. Every fact about `S` is carried through every
later effectful step and scanned by the memory simprocs, so a cluttered state is also slow.

- **Clear what is dead.** `consuming h` on the step that uses a fact for the last time (a read
  fact once its value is loaded and named, a temporary's `Fits` once it is freed); `clear h` for
  facts no later step needs (the entry state's facts once the end has what it needs);
  `clear_reads` before `subst_vars`.
- **Name values, not expressions.** C variables `with x`; a callee's stored result named right
  after the call (`name_limbs x`); unnamed values only where they are used once.
- **State facts through abstractions.** One predicate per C object (`s.mem.LimbsFit p` for a
  field element, a point predicate over its four coordinates), read and write functions per
  object (`readLimbs`, `storeLimbs`), so facts, steps and `hS` speak about objects, not bytes.
- **Abbreviate repeated structure.** A loop header's env as `abbrev hdr … E i := E[…]`, a block's
  effect as `abbrev mulSqr … S`, a callee's spec as a named function, never its unfolded body.
- **Put arithmetic in lemmas.** Overflow facts, invariant transitions and limb identities are
  separate lemmas applied by name; nothing in the step context runs `bv_decide`, `omega` or
  `ring` over the whole context.

## Critical pitfalls

1. **A named value that is stored**: `hS` then mentions it and `subst_vars` cannot eliminate it.
   Name stored values `with transparent`.
2. **A lemma over an expanded expression** no longer matches a folded `with x` operand: name it
   `transparent`, or pass `[hx]` to the step.
3. **"operand … is not known to be `.value _`"**: an earlier step left an `if … then .poison`
   (unproved overflow flag or `gep` wrap). Fix that step, not this one.
4. **Extra goals after a step** are facts that could not be carried to the new state. Register a
   `mlir_transport` lemma for that predicate and state shape instead of proving each by hand.
5. **`step_loop` warns that `S` is substituted**: the lemma's state does not match `S`; restate
   the lemma over a free state, or the shape the steps leave.
6. **`func_init` took the framed path** although nothing is allocated: the spec's final state is
   not WF by `simp [mlir_mem, *]`; add the `mlir_mem` WF lemma for the new store function.
7. **"(kernel) deep recursion"** at the theorem with fine elaboration: a value was substituted
   back (`generalize`, `subst` of a computed equation) and the kernel evaluates it. Keep such
   values opaque (`obtain ⟨b, hb⟩ : ∃ b, e = b := ⟨_, rfl⟩`).
8. **Timeout "at `whnf`" at the declaration**: implicit pointer arguments unified by evaluating
   offset arithmetic. Pass them explicitly, or add an `rfl` lemma (`(f p k).id = p.id`) and rewrite.
9. **`bv_decide` fails with "unknown free variable"**: a `let` in context plus a `∀ …, … → …`
   hypothesis mentioning it (Lean bug since nightly-2026-08-04). Clear the hypothesis, or prove the
   fact as a separate lemma.
10. **A `local macro` between theorems** waits for every proof above it (7.9 s → 6.3 s on
    pow22523 by moving them up).

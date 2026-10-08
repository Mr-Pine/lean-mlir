# Performance

Targets: a leaf function in a few seconds, a large one under a minute; appending a tactic at the
end of a proof answers in well under a second.

## Finding the slow step

1. **`lean_profile_proof`** on the theorem's line: the slowest lines and time per category
   (`simp`, `type checking`, `instantiate metavars`, …). It re-elaborates the theorem alone with
   the file's imports, so a theorem using a macro or lemma defined earlier in the same file fails
   there, and it does not find `public theorem` declarations ("No theorem/lemma/def at line N");
   use 2 for those.
2. **`set_option trace.profiler true in`** before the theorem, then `lean_diagnostic_messages`
   (info) on its line: the profiler tree per tactic. For attribution by nesting, the JSON variant
   needs flags on the command line: `lake env lean -Dtrace.profiler=true
   -Dtrace.profiler.threshold=100 -Dtrace.profiler.output=out.json F.lean` (Firefox-profiler
   format; aggregate self time per stack path). Self time in `runFrontend` and
   `Meta.realizeConst` is waiting on other proofs, not work.
3. **Cut with `sorry`** after each phase and compare totals: finds the phase, including kernel
   time, which the profilers above do not show. A proof whose tactics are fast but whose
   declaration stays busy is in the kernel.
4. **Unfold counts**: `set_option diagnostics true in <tactic>` at two positions, to see what a
   tactic unfolds and whether it grows with the position.

Measure wall time on one theorem at a time: a file's theorems elaborate in parallel, so speeding
one theorem saves CPU, not the file's wall time.

## Known slow patterns

In the proof:

| Pattern | Cost | Fix |
| --- | --- | --- |
| `local macro` between theorems | waits for every proof above it | all macros before the first theorem |
| unnamed values everywhere | `hE`/`hS` grow every step, each step re-simplifies them | name the C variables |
| facts about dead objects | every effectful step carries each fact | `consuming`, `clear` (`SKILL.md`) |
| `simp_all`, `simp … at *`, `bv_omega` in a step context | normalizes hundreds of hypotheses (38 s for 10 sites once) | `decide` for literal goals; normalize the goal only, then `omega` |
| `bv_decide`/`ring`/`omega` inside the step proof | runs in the big context | separate lemma, applied by name |
| `x[i]` with a non-literal index | core's `get_elem_tactic` runs `rw … at *` over the context | literal indices, or the bound as a named fact |
| `exact` of a whole-vector lemma that may not match | a failing unification unfolds under `ofFn` for minutes | check operand shapes first; pass arguments explicitly |
| unifying pointers (`(f p k).id =?= p.id`) | `whnf` evaluates offset arithmetic; timeout at the declaration | `rfl` lemma `(f p k).id = p.id`, rewrite explicitly |
| `generalize`/`subst` of a computed value | kernel evaluates it back ("deep recursion") | `obtain ⟨b, hb⟩ : ∃ b, e = b := ⟨_, rfl⟩` |
| `obtain`/`rcases` on big goals | reverts the goal per layer | continuation-form lemmas, `refine` |
| editing a module many files import | every importer rebuilds | stage new lemmas in the working file, move them when done |
| inputs read below many `alloca`s | each read walks every layer, each step (a call 860 ms) | read facts of the inputs right after `func_init` (220 ms) |
| a callee premise derived from a composite fact (`LimbsFit (a.add 80)` from `PointFit a`) | `mem_fact`'s transport search through `hS`, ~290 ms per premise | `mlir_transport` projection lemmas (tried two deep on the current facts first), or the coordinate facts as locals |

In the framework (fixed; check these first if a step itself is slow):

- nested generalization of state terms blows up `instantiateMVars`: keep one flat state;
- fact preservation by tactic search (~14 ms per fact per step), replaced by a MetaM fast path;
- `simp` dischargers re-scanning the context per side condition: build the fact map once;
- reads walked through every written value by `simp`: `readThroughWrites` jumps a run of writes
  in one definitional step;
- `decide +kernel` for positions: plain `decide` below 64 instructions;
- `isTypeCorrect` in `generalizeOpaque` (a third of a walk).

To stage a tactic change without rebuilding the framework, add the changed rule to a copy of the
proof file (`elab_rules`/`macro_rules` for the tactic's syntax; the newest rule is tried first)
and time it next to an unmodified copy.

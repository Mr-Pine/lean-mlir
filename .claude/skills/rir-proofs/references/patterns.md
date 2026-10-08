# Proof patterns

Each pattern with a worked example from the existing proofs (file named per pattern).
Statements are abbreviated with `…` where `specs.md` shows them in full.

## P1. Straight-line leaf (`fiat_25519_add.lean`)

Loads, arithmetic, stores, return. The steps follow the instructions; the final state is the
spec's after unfolding the store function.

```lean
  func_init
  block_init
  step_load
  step_load
  step_pure
  iterate 4
    step_pure
    step_load
    step_pure
    step_load
    step_pure
  step_store
  iterate 4
    step_pure
    step_store
  finish_block
  rw [hS, MemoryState.storeLimbs]
  congr
```

## P2. Leaf with flagged arithmetic (`fiat_25519_carry.lean`)

Each `nsw`/`nuw` the code carries is a no-overflow lemma over the operand shapes the steps
produce, proved once by `bv_decide`, registered `@[simp]` (or passed as a step's simp arg when it
needs hypotheses). Values are named after the C variables; the shifts the lemmas match on stay
unnamed (`opaque`), so the lemmas see `x >>> 51`.

```lean
@[simp]
theorem shift_mul19_mask_uaddOverflow (x y : BitVec 64) :
    ¬(x >>> 51 * 19#64).uaddOverflow (y &&& 2251799813685247#64) := by bv_decide

  -- x6 = ((x1 & UINT64_C(0x7ffffffffffff)) + ((x5 >> 51) * UINT8_C(0x13)));
  step_pure opaque
  step_pure opaque
  step_pure
  step_pure with x6
  …
  finish_block
  simp only [hS, fiat_25519_carry.spec, MemoryState.storeLimbs, MemoryState.readLimbs]
  dsimp
  congr <;> simp [*]
```

## P3. Wrapper over callees (`fd_f25519_add.lean`)

One `step_call` per call; the end combines the callees' writes with the store/read lemmas.

```lean
  func_init
  have hr₀ : S₀.mem.LimbsFit r := hS ▸ hr
  block_init
  step_call using fiat_25519_add.call_eq
  step_call using fiat_25519_carry.call_eq
  finish_block
  subst_vars
  simp [MemoryState.readLimbs_storeLimbs_self hr₀, MemoryState.storeLimbs_storeLimbs_self hr₀.1]
```

When a call's result feeds the next calls, name it (`name_limbs x` after the `step_call`) so the
state reads `storeLimbs t x` rather than the callee's spec term.

## P4. Stack temporaries (`copy_via_tmp.lean`, `fd_f25519_pow22523.lean`)

`step_alloca` gives the slot with its `Fits` and offset; build the object predicate from them
before the calls that need it. The final state counts the allocated blocks; the frame is erased at
the end.

```lean
  step_alloca
  have hv0_limbs := MemoryState.LimbsFit.of_fits hv0_fits hv0_off
  step_pure
  step_call using fd_f25519_set.call_eq
  step_call using fd_f25519_set.call_eq
  step_pure
  finish_block
  subst_vars
  simp [mlir_frame, ← GlobalState.allocaPtr_eq_slot, *]
```

Register the store function's lemmas so the steps and the frame erase see through it:
`mlir_state` (reads through it), `mlir_transport` (fit and WF facts carried past it),
`mlir_frame`/`mlir_erase` (`eraseFrom` past it, a write into an erased block dropped).

## P5. Globals (`fd_ed25519_point_set_zero.lean`)

The global's value from its folded constant, the slot read back as the object, then the object's
predicate:

```lean
public theorem fd_f25519_zero.value_eq (s : GlobalState) :
    fd_f25519_zero.value s = .value (Ty.wrap fd_f25519_zero.lit, s) :=
  GlobalInitializer.compute_value _ _ ⟨_, by with_unfolding_all rfl⟩

  step_addressof fd_f25519_zero.value_eq with zero
  have hzero_read : S.mem.readLimbs zero = f25519ZeroLimbs := by
    rw [MemoryState.readLimbs_of_readAt_flattenRaw hzero_fits hzero_off hread_zero]
    funext ⟨i, hi⟩
    match i, hi with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => rfl
  have hzero_limbs := MemoryState.LimbsFit.of_fits hzero_fits hzero_off
  …
  finish_block
  subst hS
  erase_frame
```

## P6. Branches (`fd_f25519_is_zero.lean`)

`finish_block` splits a `cond_br`/`switch` into goals tagged `isTrue`/`isFalse…`. Work through
targets with `case`, keep each condition under its own name before the next split reuses `hbr`,
and put the spec reasoning per exit in lemmas outside the proof:

```lean
theorem zero_path_broken {S₀ : GlobalState} {x} {i : Fin 5} (h0 : S₀.mem.readAt x 64 = 0)
    (hnz : ¬S₀.mem.readAt (x.add (8 * i)) 64 = 0) :
    fd_f25519_is_zero.spec (S₀.mem.readLimbs x) = 0#32 := …

  step_load
  finish_block <;> block_init
  case isFalse.isFalse =>
    finish_block
    block_init
    finish_block
    …
  all_goals
    have hbr0 := hbr
    step_pure
    step_load
    step_pure
    finish_block <;> block_init
    case isFalse =>
      …
      first
        | rw [zero_path_broken (i := 1) hbr0 hbr]
        | rw [p_path_broken (i := 1) hbr0 hbr]
```

## P7. A counted loop (`sum_limbs.lean`)

A lemma about the loop header, in continuation form, by induction on the iterations left `n`
with the counter `k` and `k + n = N`; the continuation premise says what the exit must give. The
exit case closes with `step_loop using hK`, the back edge with `step_loop using ih …`:

```lean
theorem sum_limbs.loop (a : Pointer) (s : GlobalState) (ha : s.mem.LimbsFit a)
    (hend : a.offset.toNat + 40 < 2 ^ 64) (K) :
    ∀ n k (acc : BitVec 64) (E : ⟪sum_limbs.Γ⟫), k + n = 5 →
      (∀ E' : ⟪sum_limbs.Γ⟫, E'.args = E.args →
        sum_limbs.runFrom (E'[%4 := .value (loopSpec (limb s.mem a) k n acc)]) 3 s = K) →
      sum_limbs.runFrom (E[%1 := .value 5#64, %2 := .value (BitVec.ofNat 64 k),
        %3 := .value (a.add (BitVec.ofNat 64 (8 * k))), %4 := .value acc]) 1 s = K
```

The spec side is a recursive function with the same shape (`loopSpec l k n acc`), so the
induction step is definitional. Use `Func.ContAt f bb E T S K` for the continuation premise when it
fits; state the env as an `abbrev` when several lemmas share it. For a loop that writes memory,
the lemma quantifies over the state and its facts (`S.WF → S.mem.LimbsFit t → …`) and the
continuation receives the state after all iterations
(`{ S with mem := S.mem.storeLimbs t (sqrN (n + 1) (S.mem.readLimbs t)) }`).

A header entered with a written env (the entry block's values, `E₀[%1 := …, …]`) matches no env
pattern: quantify over the env, with its args and the registers the loop reads as facts, and give
the continuation the exit's state through an equation (`fd_ed25519_point_dbln.lean`):

```lean
theorem loop (r a tp : Pointer) (n : BitVec 32) (g : Vals [.ptr] × GlobalState → PoisonOr β)
    (K : PoisonOr β) :
    ∀ m k (t : PointLimbs) (S : GlobalState) (E : ⟪Γ⟫),
      E.args = (args (.value r) (.value a) (.value n)).get →
      (E ⊨ [%2 := tp, %6 := BitVec.ofNat 8 k]) → k + m + 1 = n.toNat →
      S.WF → S.mem.PointFit r → S.mem.PointFit tp → r.id ≠ tp.id → S.mem.readPoint tp = t →
      (∀ (E' : ⟪Γ⟫) (S' : GlobalState), E'.args = (args (.value r) (.value a) (.value n)).get →
        (E' ⊨ [%2 := tp]) →
        S' = { alloc := ⟨S.alloc.nextFreeBlock + 5 * (m + 1)⟩, mem := … } →
        (fd_ed25519_point_dbln.runFrom E' ^bb1 S' >>= g) = K) →
      (fd_ed25519_point_dbln.runFrom E ^bb2 S >>= g) = K
```

The caller proves the read facts with `env_reads`. The back edge applies `ih` with the
continuation `fun E' S' h1 h2 h3 => hK E' S' h1 h2 (h3.trans ?_)` and closes the state equation
with the store lemmas; the exit applies `hK`.

## P8. Many loops of one shape (`fd_f25519_pow22523.lean`)

State one iteration (`LoopIter`) and the whole loop (`Loop`) as `abbrev`s over the header, exit,
envs and counts; prove `Loop` from `LoopIter` once (`loop_of_iter`, by induction); then each loop is
a `LoopIter` instance proved by one macro. The main proof applies each loop with `step_loop` and
names the result.

```lean
set_option hygiene false in
/-- An iteration: square, count, test; then exit or go around. -/
local macro "iter_proof" : tactic => `(tactic| (
  intro i S E hwf ht hi hexit hback
  dsimp only [hdr2, hdr4, hdr6, hdr8, hdr10, hdr12, hdr14]
  block_init
  step_call using fd_f25519_sqr.call_eq
  step_pure [saddOverflow_ofNat_one (i := i) (by omega),
    uaddOverflow_ofNat_one (i := i) (by omega)]
  step_pure
  finish_block
  · step_loop using hexit (by simp [BitVec.toNat_eq] at hbr; omega)
  · step_loop using hback (by simp [BitVec.toNat_eq] at hbr; omega)
    exact (BitVec.ofNat_add i 1).symm))

theorem iter2 (t0 t1 t2 : Pointer) :
    LoopIter 2 1 t1 5 (hdr2 t0 t1 t2) (exit2 t0 t1 t2) (β := β) g K := by
  iter_proof

-- main proof
  loop l9 using iter2 3          -- step_loop using loop_of_iter (iter2 _ _ _) 3 1; name_limbs l9
  between l10 l11 using block1
```

All macros are defined before the first theorem (a macro between theorems waits for every proof
above it).

## P9. Callee as a parameter (`fd_ed25519_point_frombytes_2x.lean`)

The lift binds the callee to a parameter; the theorem takes its spec (`specs.md`) and a transport
fact for its result state; `step_call using hspec.1`, then a case split on the callee's outcome:

```lean
  step_call using hspec.1
  cases hok : ok h0 buf0 S₀
  case false =>
    step_pure [hok]
    finish_block
    …
```

## P10. A recurring instruction run (`Avx512/FoldUnsigned.lean`)

An inlined helper that recurs: define its instructions over register variables
(`def foldRun (x m s p k a b c r : Dst Γ V) : List (Instr Γ)`), prove one lemma by the steps over
an abstract block with the body fact, and `step_pattern using runBodyFrom_foldRun with z` at each
site (statement in `tactics-guide.md` §10). The lemma's conclusion is continuation-form, its
intermediates universally quantified in the continuation so the site clears them.

Abstract registers work when every operand is a `Dst` (a value register), kept apart by a
`Nodup` premise, or a pointer `p : Reg Γ .ptr` (an argument or a value, `Avx512/Common/Point.lean`'s
`foldUnsignedStoreRun`), with `p ≠ .val q.i q.h` for each pointer register `q` written before a read
of `p`. A pattern lemma's proof may step another pattern (`dblRun` nests `foldSignedRun`): its
`Nodup` premise over the inner registers is then a premise of the outer lemma, closed by `decide`
at the site. Repeated read premises can be an `abbrev … := E ⊨ […]` (`FoldSignedConsts`).

## P11. Callee results named (`fd_f25519_pow22523.lean`)

```lean
/-- A square, its result's limbs named `x`. -/
local macro "sqr " x:ident : tactic => `(tactic| (
  step_call using fd_f25519_sqr.call_eq
  name_limbs $x))
```

After `sqr l1; sqr l2; mul l4 …`, `hS` is `storeLimbs t1 l2 (storeLimbs t0 l1 …)` with
`hl2 : l2 = fiat_25519_carry_square.spec l1`, and the final equation closes by `clear_reads;
subst_vars; rfl` against the spec's `let`s.

## P13. Aliased arguments (`fd_f25519_set.lean`, `fd_ed25519_point_neg.lean`)

When a caller passes the same object twice (`fd_ed25519_point_neg(A, A)` in verify), state one
theorem whose separation premise allows it, `hsep : dst = src ∨ dst.id ≠ src.id`, and prove it by
`rcases hsep with rfl | hsep` with the same steps in both branches. `mem_fact` cannot prove a
disjunction, so a caller names the case: `step_call using (fd_f25519_set.call_eq (hsep := .inr ?_))`
(the `?_` is closed like any premise) or `(hsep := .inl rfl)`.

## P14. Objects made of objects (`Common/Point.lean`)

A struct of field elements gets its own read/store functions and fit predicate (`readPoint`,
`storePoint` in the order the code stores, `PointFit`), plus:
- `mlir_transport` projections from the predicate to each component's (`PointFit.limbsFit_Y`),
  so `mem_fact` proves a callee's `LimbsFit (r.add 40#64)`;
- `mlir_read` lemmas for reading one component past a store to another
  (`readLimbs_storeLimbs_coord`), with premises the steps discharge: the object predicate of the
  memory before the store, and literal offset conditions by `decide`;
- read-back lemmas for the whole store (`readLimbs_storePoint_Y`), transport and frame lemmas.

Then `step_call` results compose into `storePoint r P` and the final equation closes by `rfl`.

## P12. Invariant arithmetic in transition lemmas

When a loop invariant carries arithmetic (a digit sum, a bound), the invariant is a predicate
with one field per fact, and each step of the loop applies a named transition lemma
(`Inner.add`, `Inner.finish`) whose proof does the `ring`/`omega`/`bv_decide` outside the step
context. The steps only write `fun hh => Inner.add (hI hh).1 hti …`.

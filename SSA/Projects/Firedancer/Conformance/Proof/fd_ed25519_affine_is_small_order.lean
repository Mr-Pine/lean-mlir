/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Conformance.Spec.fd_ed25519_affine_is_small_order
import SSA.Projects.Firedancer.Conformance.Rel
import SSA.Projects.Firedancer.Conformance.Proof.fd_ed25519_point_to
import SSA.Projects.Firedancer.Conformance.Proof.fd_f25519_is_zero
import SSA.Projects.Firedancer.Conformance.Proof.fd_f25519_eq

/-!
# `fd_ed25519_affine_is_small_order`: ref ≡ avx512, relationally

The pilot for the relational style. The two regions agree op for op, so the
proof never states what either side computes -- it carries `Corr` across the
five calls and reads equal `i32`s out the other end.

## The walk

Both regions, in lockstep (ref SSA numbering; the AVX-512 one matches except
for the dead `%1`--`%5` / `%7`--`%11` chains, which it drops -- see the note in
`Avx512/Mlir/Point/fd_ed25519_affine_is_small_order.lean`):

| step | op | discharged by |
|---|---|---|
| 1 | `%6`, `%12` `addressof` | `GlobalPtr`; reads the symbol table, moves no state |
| 2 | `%13`--`%16` four `alloca`s | `peel_alloca_chain`, both sides; the counts match, so the allocators stay in step |
| 3 | `%17` `call @fd_ed25519_point_to` | `fd_ed25519_point_to` (conformance, already proven) — extends `Corr` with `(x, x')` and `(y, y')` |
| 4 | `%17`, `%18` `call @fd_f25519_is_zero` | `fd_f25519_is_zero` — equal `i32` from `Corr.get` |
| 5 | `%20`, `%22` `call @fd_f25519_eq` | `fd_f25519_eq` — equal `i32`, the globals' pair out of `Corr` |
| 6 | `%19`, `%21`, `%23` `llvm.or` | equal operands, so equal results: plain `congr` |
| 7 | `lifetime.end` ×4, `return` | `peel_lifetime`; neither side's state moved observably |

Steps 3--5 are the only ones with content, and each is exactly one existing
conformance theorem. Step 6 is where a two-specification proof would instead
have had to say what the four predicates *mean*; here they are opaque `i32`s
that happen to be equal, which is all `llvm.or` needs.

`z` (`%15`) and `t` (`%16`) are written by `fd_ed25519_point_to` and never read
back, so they never enter `Corr` -- only their blocks' distinctness matters,
which `peel_alloca_chain` supplies.

## Stepping the two regions in lockstep

Both runs, and both state existentials, are kept under a *single* goal:

```
⊢ ∃ t t',
    run (Ref.<region>.denote …) s  = .value (.value ?r ::ₕ .nil, t) ∧
    run (Avx512.<region>.denote …) s' = .value (.value ?r ::ₕ .nil, t') ∧
    (s ≈ s.popFrame t.mem ∧ s' ≈ s'.popFrame t'.mem)
```

`Corr.run_runFunction₂` is what gets here: it strips `runFunction` from both
sides at once. The one-sided `run_runFunction'` applied to each conjunct would
do the same arithmetic but split the goal per backend, and once split each side
must be walked alone -- `Corr` then has nowhere to live and degenerates into a
bundle of hypotheses reconciled after the fact.

Kept together, the walk peels one op from each region at a time, re-establishing
the relation as it goes: the shared `?r` is the one value the two sides must
agree on, and `t`/`t'` stay existential so no step has to name a state before
the walk reaches it. `Corr.frame` is what each call step spends -- a callee that
writes outside `φ` leaves the invariant standing.

The op sequences correspond exactly (ref numbering; AVX-512 matches):

| step | op | discharged by |
|---|---|---|
| 1 | `%6`, `%12` `addressof` | `GlobalPtr`; reads the symbol table, moves no state |
| 2 | `%13`--`%16` four `alloca`s | `peel_alloca_chain` on each side; the counts match, so the allocators stay in step |
| 3 | `call @fd_ed25519_point_to` | `fd_ed25519_point_to` conformance; extends `Corr` with `(x, x')` and `(y, y')` |
| 4 | `%17`, `%18` `call @fd_f25519_is_zero` | `fd_f25519_is_zero` conformance; equal `i32` from `Corr.get` |
| 5 | `%20`, `%22` `call @fd_f25519_eq` | `fd_f25519_eq` conformance; the globals' pair out of `Corr` |
| 6 | `%19`, `%21`, `%23` `llvm.or` | equal operands, so equal results |
| 7 | `lifetime.end` x4, `return` | `peel_lifetime`; neither state moved observably |

Steps 3--5 are the only ones with content, and each is one existing conformance
theorem -- already in the continuation form (`∃ s', run … = .value ([r]ₕ, s')
∧ … ≈ s'`) that the call steps consume. Step 6 is where a two-specification
proof would have had to say what the four predicates *mean*; here they are
opaque `i32`s that happen to be equal, which is all `llvm.or` needs.

`z` (`%15`) and `t` (`%16`) are written by `fd_ed25519_point_to` and never read
back, so they never enter `Corr`; only their blocks' distinctness matters.

## Status

Done and sorry-free: the invariant, the statement, both region lifts, the
`runFunction` strip on each side, the alloca transports and `Nodup`s, and the
walk on both regions through the `fd_ed25519_point_to` call -- ref stepped with
`v`, AVX-512 with `u`, each via `focus_left`/`focus_right`
(`Conformance/Rel.lean`). Both runs now stand at the first `fd_f25519_is_zero`
in the post-call states `sR`/`sA`; `heqR`/`heqA` relate those to the four-splice
chains, and `hvX`… / `hvX'`… give the slots' values there.

Remaining: `is_zero(x)`, `is_zero(y)`, `eq(y, y0)`, `eq(y, y1)` on both sides,
the three `or`s, the four `lifetime.end`s, the return -- then delete
`case r => sorry`.

Two rules this file learned the hard way: step with `denote_step_all`, never
`denote_step_reduce` (its `reduce_hv` pass chokes on the 320/512-bit
initialiser constants); and at an alloca'd call site apply
`run_bind_denote_call_cfg_of_{nil,value}` by hand with `argTys`, `argVals` and
`s'` pinned -- `peel_call` falls through to a whole-program `whnf` and exhausts
the heartbeat budget, exactly as `sllvm-proof-elaboration-cost` records.
-/

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

set_option maxHeartbeats 4000000 in
theorem fd_ed25519_affine_is_small_order :
    fd_ed25519_affine_is_small_order_equivalent := by
  unfold fd_ed25519_affine_is_small_order_equivalent
  intro s a g0 g1 hs ha haLimbs hg0 hg1 hg0f hg1f hg0b hg1b hgne refResult
  intro s' a' g0' g1' hs' ha' hXr hYr hg0' hg1' hg0f' hg1f' hg0r hg1r hgne' avxResult
  intro hpoint hy0 hy1

  -- The invariant the walk carries: the two order-8 globals, related. The
  -- point's copies join it at step 3, once `fd_ed25519_point_to` has run.
  have hcorr : Corr s s' [(g0, g0'), (g1, g1')] :=
    { wf := hs
      wf' := hs'
      nodup := by simpa using hgne
      nodup' := by simpa using hgne'
      pairs := by
        intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact ⟨hg0f, hg0f', hy0⟩
        · exact ⟨hg1f, hg1f', hy1⟩ }

  -- One shared result `r` out in front, then a separate existential per
  -- backend. Each conjunct is `∃ t, run … = .value ([r]ₕ, t) ∧ P t`, which is
  -- exactly what `run_runFunction'` consumes.
  suffices h : ∃ r : BitVec 32,
      (∃ sOut, StateT.run (runFunction (Ref.fd_ed25519_affine_is_small_order.denote
          (Ctxt.Valuation.singleton (.value a)))) s
        = .value ([(PoisonOr.value r : LLVM.IntW 32)]ₕ, sOut) ∧ s ≈ sOut)
      ∧ (∃ sOut', StateT.run (runFunction (Avx512.fd_ed25519_affine_is_small_order.denote
          (Ctxt.Valuation.singleton (.value a')))) s'
        = .value ([(PoisonOr.value r : LLVM.IntW 32)]ₕ, sOut') ∧ s' ≈ sOut') by
    obtain ⟨r, ⟨sOut, hr, he⟩, ⟨sOut', hr', he'⟩⟩ := h
    exact ⟨r, sOut, sOut', hr, hr', he, he'⟩

  existsi ?r
  rotate_left
  refine And.imp_left (run_runFunction' (s ≈ ·)) ?_
  refine And.imp_right (run_runFunction' (s' ≈ ·)) ?_

  -- One goal, both raw region walks, `?r` shared between them: the shape a
  -- lockstep walk needs.
  --
  -- Step 2, both sides. The regions allocate `x, y, z, t` in the same order and
  -- the same number, so the two allocators advance in step -- ref at 320 bits a
  -- slot, AVX-512 at 512.
  obtain ⟨xr, r1, hxrdef, hr1, hr1WF, hxrfits, hxrid, hxroff, hr1next, hr1live⟩ :=
    GlobalState.exists_afterAlloca_facts s hs 320
  obtain ⟨yr, r2, hyrdef, hr2, hr2WF, hyrfits, hyrid, hyroff, hr2next, hr2live⟩ :=
    GlobalState.exists_afterAlloca_facts r1 hr1WF 320
  obtain ⟨zr, r3, hzrdef, hr3, hr3WF, hzrfits, hzrid, hzroff, hr3next, hr3live⟩ :=
    GlobalState.exists_afterAlloca_facts r2 hr2WF 320
  obtain ⟨tr, r4, htrdef, hr4, hr4WF, htrfits, htrid, htroff, hr4next, hr4live⟩ :=
    GlobalState.exists_afterAlloca_facts r3 hr3WF 320

  obtain ⟨xa, w1, hxadef, hw1, hw1WF, hxafits, hxaid, hxaoff, hw1next, hw1live⟩ :=
    GlobalState.exists_afterAlloca_facts s' hs' 512
  obtain ⟨ya, w2, hyadef, hw2, hw2WF, hyafits, hyaid, hyaoff, hw2next, hw2live⟩ :=
    GlobalState.exists_afterAlloca_facts w1 hw1WF 512
  obtain ⟨za, w3, hzadef, hw3, hw3WF, hzafits, hzaid, hzaoff, hw3next, hw3live⟩ :=
    GlobalState.exists_afterAlloca_facts w2 hw2WF 512
  obtain ⟨ta, w4, htadef, hw4, hw4WF, htafits, htaid, htaoff, hw4next, hw4live⟩ :=
    GlobalState.exists_afterAlloca_facts w3 hw3WF 512

  -- Transport the four ref slots to `r4`. Each was allocated below the counter
  -- the later allocas start from, so `FrameBelow` carries it across them.
  have fbr1 : FrameBelow r1.alloc.nextFreeBlock r1 r4 := by
    have h2 : FrameBelow r1.alloc.nextFreeBlock r1 r2 :=
      hr2 ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
    have h3 : FrameBelow r1.alloc.nextFreeBlock r1 r3 :=
      hr3 ▸ FrameBelow.afterAlloca (by omega) h2
    exact hr4 ▸ FrameBelow.afterAlloca (by omega) h3
  have fbr2 : FrameBelow r2.alloc.nextFreeBlock r2 r4 := by
    have h3 : FrameBelow r2.alloc.nextFreeBlock r2 r3 :=
      hr3 ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
    exact hr4 ▸ FrameBelow.afterAlloca (by omega) h3
  have fbr3 : FrameBelow r3.alloc.nextFreeBlock r3 r4 :=
    hr4 ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)

  have hxr4 : Ref.IsFieldElemPtr r4.mem xr :=
    Ref.isFieldElemPtr_of_live?_eq (fbr1 xr.id (by omega)) ⟨hxrfits, by rw [hxroff]; simp⟩
  have hyr4 : Ref.IsFieldElemPtr r4.mem yr :=
    Ref.isFieldElemPtr_of_live?_eq (fbr2 yr.id (by omega)) ⟨hyrfits, by rw [hyroff]; simp⟩
  have hzr4 : Ref.IsFieldElemPtr r4.mem zr :=
    Ref.isFieldElemPtr_of_live?_eq (fbr3 zr.id (by omega)) ⟨hzrfits, by rw [hzroff]; simp⟩
  have htr4 : Ref.IsFieldElemPtr r4.mem tr := ⟨htrfits, by rw [htroff]; simp⟩

  -- ... and the four AVX-512 slots to `w4`, the same way. `IsVecPtr` is
  -- `Fits ∧ offset bound`, so it transports with `fits_of_live?_eq` directly.
  have fbw1 : FrameBelow w1.alloc.nextFreeBlock w1 w4 := by
    have h2 : FrameBelow w1.alloc.nextFreeBlock w1 w2 :=
      hw2 ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
    have h3 : FrameBelow w1.alloc.nextFreeBlock w1 w3 :=
      hw3 ▸ FrameBelow.afterAlloca (by omega) h2
    exact hw4 ▸ FrameBelow.afterAlloca (by omega) h3
  have fbw2 : FrameBelow w2.alloc.nextFreeBlock w2 w4 := by
    have h3 : FrameBelow w2.alloc.nextFreeBlock w2 w3 :=
      hw3 ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
    exact hw4 ▸ FrameBelow.afterAlloca (by omega) h3
  have fbw3 : FrameBelow w3.alloc.nextFreeBlock w3 w4 :=
    hw4 ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)

  have hxa4 : Avx512.IsVecPtr w4.mem xa :=
    ⟨fits_of_live?_eq (fbw1 xa.id (by omega)) hxafits, by rw [hxaoff]; simp⟩
  have hya4 : Avx512.IsVecPtr w4.mem ya :=
    ⟨fits_of_live?_eq (fbw2 ya.id (by omega)) hyafits, by rw [hyaoff]; simp⟩
  have hza4 : Avx512.IsVecPtr w4.mem za :=
    ⟨fits_of_live?_eq (fbw3 za.id (by omega)) hzafits, by rw [hzaoff]; simp⟩
  have hta4 : Avx512.IsVecPtr w4.mem ta := ⟨htafits, by rw [htaoff]; simp⟩

  -- The two input points predate their own side's allocas, so each survives
  -- its four of them.
  have fbs : FrameBelow s.alloc.nextFreeBlock s r4 := by
    have h1 : FrameBelow s.alloc.nextFreeBlock s r1 :=
      hr1 ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
    have h2 : FrameBelow s.alloc.nextFreeBlock s r2 := hr2 ▸ FrameBelow.afterAlloca (by omega) h1
    have h3 : FrameBelow s.alloc.nextFreeBlock s r3 := hr3 ▸ FrameBelow.afterAlloca (by omega) h2
    exact hr4 ▸ FrameBelow.afterAlloca (by omega) h3
  have fbs' : FrameBelow s'.alloc.nextFreeBlock s' w4 := by
    have h1 : FrameBelow s'.alloc.nextFreeBlock s' w1 :=
      hw1 ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
    have h2 : FrameBelow s'.alloc.nextFreeBlock s' w2 := hw2 ▸ FrameBelow.afterAlloca (by omega) h1
    have h3 : FrameBelow s'.alloc.nextFreeBlock s' w3 := hw3 ▸ FrameBelow.afterAlloca (by omega) h2
    exact hw4 ▸ FrameBelow.afterAlloca (by omega) h3

  have ha4 : Ref.IsPointPtr r4.mem a :=
    Ref.isPointPtr_of_live?_eq (fbs a.id (lt_nextFreeBlock_of_fits hs ha.left)) ha
  have ha4' : Avx512.IsQuadPtr w4.mem a' :=
    ⟨fits_of_live?_eq (fbs' a'.id (lt_nextFreeBlock_of_fits hs' ha'.left)) ha'.left, ha'.right⟩

  -- The four slots get consecutive block ids and each input point predates
  -- them, so both `Nodup`s are id arithmetic.
  have hlt : a.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs ha.left
  have hNodupR : ([xr, yr, zr, tr, a].map Pointer.id).Nodup := by
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or, List.nodup_nil, and_true]
    and_intros <;>
      first
        | exact fun h => absurd (congrArg BlockId.id h) (by omega)
        | exact id
  have hNodupA : ([xa, ya, za, ta].map Pointer.id).Nodup := by
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or, List.nodup_nil, and_true]
    and_intros <;>
      first
        | exact fun h => absurd (congrArg BlockId.id h) (by omega)
        | exact id

  -- Step 3, both sides: `fd_ed25519_point_to`. Each side's conformance theorem
  -- is already in continuation form, so this is where the walk actually spends
  -- an existing result rather than bookkeeping.
  have hptR := Ref.fd_ed25519_point_to_conforms xr yr zr tr a r4 hr4WF hNodupR ha4
    hxr4 hyr4 hzr4 htr4
  have hptA := Avx512.fd_ed25519_point_to_conforms xa ya za ta a' w4 hw4WF hNodupA ha4'
    hxa4 hya4 hza4 hta4


  -- Expose both regions' block bodies so the peel lemmas have something to
  -- rewrite. Both `StateT.run` terms sit under the conjunction; each `peel_*`
  -- is a `rw`, so it targets whichever side's term it matches -- no splitting.
  simp only [Ref.fd_ed25519_affine_is_small_order,
    Avx512.fd_ed25519_affine_is_small_order, Cfg.denote]

  -- `%0`--`%5` on each side, ref stepped with `v`, AVX-512 with `u`. Each
  -- focus returns to the combined goal with that side's `v_i`/`u_i` and their
  -- defining equations in scope -- `focus_*` lifts the definitions out.
  -- (`denote_step_reduce` cannot be used here: its `reduce_hv` pass chokes on
  -- the 320/512-bit initialiser constants.)
  focus_left
    denote_step_all v 5
    peel_addressof hg0
  focus_right
    denote_step_all u 5
    peel_addressof hg0'

  -- `%7`--`%16` and the lifetimes, up to the `fd_ed25519_point_to` call: the
  -- second dead initialiser chain, `addressof @…_y1`, the four allocas landing
  -- in the states named up front (`r1…r4` / `w1…w4`), and four
  -- `lifetime.start`s that move no state.
  focus_left
    denote_step_all v 11
    peel_addressof hg1
    peel_alloca from s as r1 with hr1
    peel_alloca from r1 as r2 with hr2
    peel_alloca from r2 as r3 with hr3
    peel_alloca from r3 as r4 with hr4
    peel_lifetime
    peel_lifetime
    peel_lifetime
    peel_lifetime
  focus_right
    denote_step_all u 11
    peel_addressof hg1'
    peel_alloca from s' as w1 with hw1
    peel_alloca from w1 as w2 with hw2
    peel_alloca from w2 as w3 with hw3
    peel_alloca from w3 as w4 with hw4
    peel_lifetime
    peel_lifetime
    peel_lifetime
    peel_lifetime

  -- The `fd_ed25519_point_to` call, both sides. Each conformance result is a
  -- run equation in continuation form; its other conjuncts say what the four
  -- slots now hold. These are plain facts, so they are taken apart *outside*
  -- the focus -- `focus_*` lifts only defining pairs -- and the call step
  -- inside is a bare `peel_call`, whose operand side goal needs the pointer
  -- definitions to see `xr` as `⟨⟨s.alloc.nextFreeBlock⟩, 0⟩`.
  obtain ⟨oX, oY, oZ, oT, ⟨sR, hrunR, heqR⟩, hlX, hlY, hlZ, hlT, hvX, hvY, hvZ, hvT⟩ := hptR
  obtain ⟨⟨sA, hrunA, heqA⟩, hwX, hwY, hwZ, hwT, hvX', hvY', hvZ', hvT'⟩ := hptA
  -- Not `peel_call`: at an alloca'd call site with this valuation it falls
  -- through to a whole-program `whnf` and exhausts the heartbeat budget
  -- (`sllvm-proof-elaboration-cost`). Name `argTys`, `argVals` and `s'` so
  -- nothing is left to unification; `hargs` closes by the spine simp set plus
  -- the pointer definitions.
  focus_left
    rw [BlockCom.run_bind_denote_call_cfg_of_nil
      (c := Ref.fd_ed25519_point_to)
      (argTys := [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr])
      (argVals := [PoisonOr.value a, PoisonOr.value tr, PoisonOr.value zr,
        PoisonOr.value yr, PoisonOr.value xr]ₕ)
      (s' := sR)
      (by simp only [simp_spine, Ctxt.Valuation.singleton, hxrdef, hyrdef, hzrdef, htrdef])
      hrunR]
  focus_right
    rw [BlockCom.run_bind_denote_call_cfg_of_nil
      (c := Avx512.fd_ed25519_point_to)
      (argTys := [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr])
      (argVals := [PoisonOr.value a', PoisonOr.value ta, PoisonOr.value za,
        PoisonOr.value ya, PoisonOr.value xa]ₕ)
      (s' := sA)
      (by simp only [simp_spine, Ctxt.Valuation.singleton, hxadef, hyadef, hzadef, htadef])
      hrunA]

  -- The input points survive their own side's four allocas.
  have hPtR : Ref.readPoint ha4 = Ref.readPoint ha :=
    Ref.readPoint_of_live?_eq (fbs a.id hlt) ha ha4
  have hPtA : Avx512.readQuad ha4' = Avx512.readQuad ha' :=
    Avx512.readQuad_of_live?_eq (fbs' a'.id (lt_nextFreeBlock_of_fits hs' ha'.left)) ha' ha4'

  -- The slot pointer facts at the two post-call memories. Every splice's
  -- `(p := ·) (x := ·)` is spelled out: left implicit, the unifier solves them
  -- by δ-unfolding `MemoryState.splice` against the four-splice memory and
  -- exhausts the heartbeat budget (`sllvm-proof-elaboration-cost`).
  have hoXR : Ref.IsFieldElemPtr ((((r4.mem.splice xr oX).splice yr oY).splice zr oZ).splice tr oT) xr :=
    Ref.isFieldElemPtr_splice (p := tr) (x := oT) (Ref.isFieldElemPtr_splice (p := zr) (x := oZ)
      (Ref.isFieldElemPtr_splice (p := yr) (x := oY) (Ref.isFieldElemPtr_splice (p := xr) (x := oX) hxr4)))
  have hoYR : Ref.IsFieldElemPtr ((((r4.mem.splice xr oX).splice yr oY).splice zr oZ).splice tr oT) yr :=
    Ref.isFieldElemPtr_splice (p := tr) (x := oT) (Ref.isFieldElemPtr_splice (p := zr) (x := oZ)
      (Ref.isFieldElemPtr_splice (p := yr) (x := oY) (Ref.isFieldElemPtr_splice (p := xr) (x := oX) hyr4)))
  have hoZR : Ref.IsFieldElemPtr ((((r4.mem.splice xr oX).splice yr oY).splice zr oZ).splice tr oT) zr :=
    Ref.isFieldElemPtr_splice (p := tr) (x := oT) (Ref.isFieldElemPtr_splice (p := zr) (x := oZ)
      (Ref.isFieldElemPtr_splice (p := yr) (x := oY) (Ref.isFieldElemPtr_splice (p := xr) (x := oX) hzr4)))
  have hoTR : Ref.IsFieldElemPtr ((((r4.mem.splice xr oX).splice yr oY).splice zr oZ).splice tr oT) tr :=
    Ref.isFieldElemPtr_splice (p := tr) (x := oT) (Ref.isFieldElemPtr_splice (p := zr) (x := oZ)
      (Ref.isFieldElemPtr_splice (p := yr) (x := oY) (Ref.isFieldElemPtr_splice (p := xr) (x := oX) htr4)))
  have hoXA : Avx512.IsVecPtr ((((w4.mem.splice xa (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.X))).splice
      ya (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y))).splice
      za (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Z))).splice
      ta (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.T))) xa :=
    Avx512.isVecPtr_splice (q := ta) (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.T))
      (Avx512.isVecPtr_splice (q := za) (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Z))
      (Avx512.isVecPtr_splice (q := ya) (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y))
      (Avx512.isVecPtr_splice (q := xa) (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.X)) hxa4)))
  have hoYA : Avx512.IsVecPtr ((((w4.mem.splice xa (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.X))).splice
      ya (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y))).splice
      za (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Z))).splice
      ta (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.T))) ya :=
    Avx512.isVecPtr_splice (q := ta) (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.T))
      (Avx512.isVecPtr_splice (q := za) (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Z))
      (Avx512.isVecPtr_splice (q := ya) (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y))
      (Avx512.isVecPtr_splice (q := xa) (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.X)) hya4)))
  have hoZA : Avx512.IsVecPtr ((((w4.mem.splice xa (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.X))).splice
      ya (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y))).splice
      za (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Z))).splice
      ta (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.T))) za :=
    Avx512.isVecPtr_splice (q := ta) (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.T))
      (Avx512.isVecPtr_splice (q := za) (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Z))
      (Avx512.isVecPtr_splice (q := ya) (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y))
      (Avx512.isVecPtr_splice (q := xa) (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.X)) hza4)))
  have hoTA : Avx512.IsVecPtr ((((w4.mem.splice xa (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.X))).splice
      ya (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y))).splice
      za (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Z))).splice
      ta (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.T))) ta :=
    Avx512.isVecPtr_splice (q := ta) (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.T))
      (Avx512.isVecPtr_splice (q := za) (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Z))
      (Avx512.isVecPtr_splice (q := ya) (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y))
      (Avx512.isVecPtr_splice (q := xa) (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.X)) hta4)))

  -- **The two backends hold the same field elements in the four slots.** Each
  -- side's spec pins the slot's value at the state the call returned in, up to
  -- `≈`; `hpoint` ties the two input points. Two disciplines keep this cheap:
  -- the values are read through `readFieldElem?`/`readVec?`, so no proof term is
  -- matched against the big memories; and the record is bound *first*, at those
  -- memories, then handed to `of_equiv` with every state explicit.
  have hcX0 : FieldCorr ((((r4.mem.splice xr oX).splice yr oY).splice zr oZ).splice tr oT) ((((w4.mem.splice xa (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.X))).splice
      ya (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y))).splice
      za (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Z))).splice
      ta (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.T))) xr xa :=
    { ref := hoXR, avx := hoXA
      value := by
        rw [Ref.readFieldElem_eq_of (h := hoXR) ((Option.some_get _).symm.trans (congrArg some hvX)),
          Avx512.readVec_eq_of (h := hoXA) ((Option.some_get _).symm.trans (congrArg some hwX)),
          hPtR, hpoint, ← hPtA]
        exact ((congrArg Avx512.vecValue hwX).symm.trans hvX').symm }
  have hcX : FieldCorr sR.mem sA.mem xr xa :=
    FieldCorr.of_equiv (s := { r4 with mem := ((((r4.mem.splice xr oX).splice yr oY).splice zr oZ).splice tr oT) }) (s' := { w4 with mem := ((((w4.mem.splice xa (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.X))).splice
      ya (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y))).splice
      za (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Z))).splice
      ta (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.T))) }) (t := sR) (t' := sA) hcX0 heqR heqA
  have hcY0 : FieldCorr ((((r4.mem.splice xr oX).splice yr oY).splice zr oZ).splice tr oT) ((((w4.mem.splice xa (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.X))).splice
      ya (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y))).splice
      za (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Z))).splice
      ta (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.T))) yr ya :=
    { ref := hoYR, avx := hoYA
      value := by
        rw [Ref.readFieldElem_eq_of (h := hoYR) ((Option.some_get _).symm.trans (congrArg some hvY)),
          Avx512.readVec_eq_of (h := hoYA) ((Option.some_get _).symm.trans (congrArg some hwY)),
          hPtR, hpoint, ← hPtA]
        exact ((congrArg Avx512.vecValue hwY).symm.trans hvY').symm }
  have hcY : FieldCorr sR.mem sA.mem yr ya :=
    FieldCorr.of_equiv (s := { r4 with mem := ((((r4.mem.splice xr oX).splice yr oY).splice zr oZ).splice tr oT) }) (s' := { w4 with mem := ((((w4.mem.splice xa (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.X))).splice
      ya (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y))).splice
      za (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Z))).splice
      ta (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.T))) }) (t := sR) (t' := sA) hcY0 heqR heqA
  have hcZ0 : FieldCorr ((((r4.mem.splice xr oX).splice yr oY).splice zr oZ).splice tr oT) ((((w4.mem.splice xa (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.X))).splice
      ya (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y))).splice
      za (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Z))).splice
      ta (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.T))) zr za :=
    { ref := hoZR, avx := hoZA
      value := by
        rw [Ref.readFieldElem_eq_of (h := hoZR) ((Option.some_get _).symm.trans (congrArg some hvZ)),
          Avx512.readVec_eq_of (h := hoZA) ((Option.some_get _).symm.trans (congrArg some hwZ)),
          hPtR, hpoint, ← hPtA]
        exact ((congrArg Avx512.vecValue hwZ).symm.trans hvZ').symm }
  have hcZ : FieldCorr sR.mem sA.mem zr za :=
    FieldCorr.of_equiv (s := { r4 with mem := ((((r4.mem.splice xr oX).splice yr oY).splice zr oZ).splice tr oT) }) (s' := { w4 with mem := ((((w4.mem.splice xa (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.X))).splice
      ya (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y))).splice
      za (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Z))).splice
      ta (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.T))) }) (t := sR) (t' := sA) hcZ0 heqR heqA
  have hcT0 : FieldCorr ((((r4.mem.splice xr oX).splice yr oY).splice zr oZ).splice tr oT) ((((w4.mem.splice xa (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.X))).splice
      ya (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y))).splice
      za (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Z))).splice
      ta (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.T))) tr ta :=
    { ref := hoTR, avx := hoTA
      value := by
        rw [Ref.readFieldElem_eq_of (h := hoTR) ((Option.some_get _).symm.trans (congrArg some hvT)),
          Avx512.readVec_eq_of (h := hoTA) ((Option.some_get _).symm.trans (congrArg some hwT)),
          hPtR, hpoint, ← hPtA]
        exact ((congrArg Avx512.vecValue hwT).symm.trans hvT').symm }
  have hcT : FieldCorr sR.mem sA.mem tr ta :=
    FieldCorr.of_equiv (s := { r4 with mem := ((((r4.mem.splice xr oX).splice yr oY).splice zr oZ).splice tr oT) }) (s' := { w4 with mem := ((((w4.mem.splice xa (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.X))).splice
      ya (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y))).splice
      za (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Z))).splice
      ta (Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.T))) }) (t := sR) (t' := sA) hcT0 heqR heqA

  -- Well-formedness of the two post-call states, through the four splices
  -- (arguments spelled out, as everywhere the four-splice memory appears).
  have hsR : sR.WF :=
    ((((hr4WF.splice (p := xr) (x := oX)).splice (p := yr) (x := oY)).splice (p := zr) (x := oZ)).splice
      (p := tr) (x := oT)).of_equiv heqR
  have hsA : sA.WF :=
    ((((hw4WF.splice (p := xa) (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.X))).splice
      (p := ya) (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y))).splice
      (p := za) (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Z))).splice
      (p := ta) (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.T))).of_equiv heqA

  -- `LimbBounds` in the `readLimb?` form the transport lemmas take.
  have limbBounds_to_read? : ∀ {m : MemoryState} {q : Pointer} (h : Ref.IsFieldElemPtr m q) {n : ℕ},
      Ref.LimbBounds h n → ∀ (j : Fin 5) (l : ℕ), Ref.readLimb? q j m = some l → l ≤ n := by
    intro m q h n hb j l hl
    have := hb j
    simp only [Ref.readLimb, hl, Option.get_some] at this
    exact this

  -- `LimbBounds` for the copied `xr` at `sR`: the input point's bound
  -- (`haLimbs 0`) survives the allocas, crosses the verbatim copy `hlX`, and
  -- rides `heqR` to `sR`.
  have hbX : Ref.LimbBounds hcX.ref := by
    have h0 := limbBounds_to_read? _ (haLimbs 0)
    rw [Ref.coordPtr_zero] at h0
    have h1 := Ref.limbBounds_of_live?_eq (fbs a.id hlt) h0
    have h2 : Ref.LimbBounds hoXR := fun i => by
      rw [hlX i]
      exact Ref.limbBounds_of_readLimb? _ h1 i
    exact Ref.limbBounds_of_equiv (s := { r4 with mem := ((((r4.mem.splice xr oX).splice yr oY).splice zr oZ).splice tr oT) }) (s' := sR) heqR h2
  -- What the AVX-512 slot reads at `sA`: the widened coordinate vector. Derived
  -- at the `readVec?` level -- a live-block equality across `heqA`, then the
  -- spec's readback -- so no two proofs of `IsVecPtr` are ever compared.
  have hvxa : Avx512.readVec hcX.avx = Avx512.widenVec (Avx512.readQuad ha4').PointVecs.X :=
    Avx512.readVec_eq_of ((Avx512.readVec?_of_live?_eq (heqA.live xa.id).symm).trans
      ((Option.some_get _).symm.trans (congrArg some hwX)))
  have hXr4 : R43x6.Reduced (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.X) := by
    rw [hPtA]; exact hXr

  -- `fd_f25519_is_zero(xr)`, both sides.
  obtain ⟨sR1, hrunR1, heqR1⟩ := Ref.fd_f25519_is_zero_conforms xr sR hsR hcX.ref hbX
  obtain ⟨sA1, hrunA1, heqA1⟩ := Avx512.fd_f25519_is_zero_conforms xa sA hsA hcX.avx
    (by rw [hvxa]; exact hXr4.nearlyReduced) (by rw [hvxa]; rfl) (by rw [hvxa]; rfl)
  -- The two results coincide: the ref test is on `readFieldElem?`, the AVX-512
  -- one on `vecValue`, and `hcX.value` says they are the same element.
  have houtX : (if Ref.readFieldElem? xr sR.mem = some 0 then 1#32 else 0#32)
      = (if Avx512.vecValue (Avx512.readVec hcX.avx) = 0 then 1#32 else 0#32) := by
    have hsome : Ref.readFieldElem? xr sR.mem = some (Ref.readFieldElem hcX.ref) :=
      (Option.some_get _).symm
    have hiff : (Ref.readFieldElem? xr sR.mem = some 0)
        ↔ (Avx512.vecValue (Avx512.readVec hcX.avx) = 0) := by
      rw [hsome, Option.some_inj, hcX.value]
    by_cases h : Avx512.vecValue (Avx512.readVec hcX.avx) = 0
    · rw [if_pos h, if_pos (hiff.mpr h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mp hc))]
  -- The AVX-512 run equation restated with the *ref* expression as its result
  -- -- that is where the two walks are tied together, and what `houtX` is for.
  have hrunA1' : StateT.run (runFunction (Avx512.fd_f25519_is_zero.denote
        (Ctxt.Valuation.singleton (.value xa)))) sA
      = .value ([(PoisonOr.value (if Ref.readFieldElem? xr sR.mem = some 0 then 1#32 else 0#32)
          : LLVM.IntW 32)]ₕ, sA1) := by
    rw [houtX]; exact hrunA1
  -- The call peels are not focused: an explicit `c := Ref.…`/`c := Avx512.…`
  -- makes the `rw` side-specific already, and the same pattern that matches
  -- the conjunct in the combined goal was not found on `focus_*`'s scratch copy.
  rw [BlockCom.run_bind_denote_call_cfg_of_value (c := Ref.fd_f25519_is_zero)
    (argTys := [SLLVM.Ty.ptr]) (argVals := (PoisonOr.value xr ::ₕ HVector.nil))
    (x := PoisonOr.value (if Ref.readFieldElem? xr sR.mem = some 0 then 1#32 else 0#32))
    (s' := sR1) (by simp only [simp_spine, Ctxt.Valuation.singleton, hxrdef]) hrunR1]
  rw [BlockCom.run_bind_denote_call_cfg_of_value (c := Avx512.fd_f25519_is_zero)
    (argTys := [SLLVM.Ty.ptr]) (argVals := (PoisonOr.value xa ::ₕ HVector.nil))
    (x := PoisonOr.value (if Ref.readFieldElem? xr sR.mem = some 0 then 1#32 else 0#32))
    (s' := sA1) (by simp only [simp_spine, Ctxt.Valuation.singleton, hxadef]) hrunA1']

  -- `LimbBounds` for the copied `yr` at `sR`: the input point's bound
  -- (`haLimbs 1`) survives the allocas, crosses the verbatim copy `hlY`, and
  -- rides `heqR` to `sR`.
  have hbY : Ref.LimbBounds hcY.ref := by
    have h0 := limbBounds_to_read? _ (haLimbs 1)
    rw [Ref.coordPtr_one] at h0
    -- the `Y` coordinate sits at `a.withOffset 40`, whose block is `a`'s
    have h1 := Ref.limbBounds_of_live?_eq (p := a.withOffset 40) (fbs (a.withOffset 40).id hlt) h0
    have h2 : Ref.LimbBounds hoYR := fun i => by
      rw [hlY i]
      exact Ref.limbBounds_of_readLimb? _ h1 i
    exact Ref.limbBounds_of_equiv (s := { r4 with mem := ((((r4.mem.splice xr oX).splice yr oY).splice zr oZ).splice tr oT) }) (s' := sR) heqR h2
  -- What the AVX-512 slot reads at `sA`: the widened coordinate vector. Derived
  -- at the `readVec?` level -- a live-block equality across `heqA`, then the
  -- spec's readback -- so no two proofs of `IsVecPtr` are ever compared.
  have hvya : Avx512.readVec hcY.avx = Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y :=
    Avx512.readVec_eq_of ((Avx512.readVec?_of_live?_eq (heqA.live ya.id).symm).trans
      ((Option.some_get _).symm.trans (congrArg some hwY)))
  have hYr4 : R43x6.Reduced (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y) := by
    rw [hPtA]; exact hYr

  -- `fd_f25519_is_zero(yr)`, both sides. The runs are now in `sR1`/`sA1`; the
  -- first `is_zero` wrote nothing (`heqR1`, `heqA1`), so everything about `y`
  -- transports across -- and the states here are plain variables, so `of_equiv`
  -- is cheap.
  have hcY1 : FieldCorr sR1.mem sA1.mem yr ya := hcY.of_equiv heqR1 heqA1
  have hsR1 : sR1.WF := hsR.of_equiv heqR1
  have hsA1 : sA1.WF := hsA.of_equiv heqA1
  have hbY1 : Ref.LimbBounds hcY1.ref := Ref.limbBounds_of_equiv heqR1 hbY
  have hvya1 : Avx512.readVec hcY1.avx = Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y :=
    Avx512.readVec_eq_of ((Avx512.readVec?_of_live?_eq (heqA1.live ya.id).symm).trans
      ((Option.some_get _).symm.trans (congrArg some hvya)))
  obtain ⟨sR2, hrunR2, heqR2⟩ := Ref.fd_f25519_is_zero_conforms yr sR1 hsR1 hcY1.ref hbY1
  obtain ⟨sA2, hrunA2, heqA2⟩ := Avx512.fd_f25519_is_zero_conforms ya sA1 hsA1 hcY1.avx
    (by rw [hvya1]; exact hYr4.nearlyReduced) (by rw [hvya1]; rfl) (by rw [hvya1]; rfl)
  have houtY : (if Ref.readFieldElem? yr sR1.mem = some 0 then 1#32 else 0#32)
      = (if Avx512.vecValue (Avx512.readVec hcY1.avx) = 0 then 1#32 else 0#32) := by
    have hsome : Ref.readFieldElem? yr sR1.mem = some (Ref.readFieldElem hcY1.ref) :=
      (Option.some_get _).symm
    have hiff : (Ref.readFieldElem? yr sR1.mem = some 0)
        ↔ (Avx512.vecValue (Avx512.readVec hcY1.avx) = 0) := by
      rw [hsome, Option.some_inj, hcY1.value]
    by_cases h : Avx512.vecValue (Avx512.readVec hcY1.avx) = 0
    · rw [if_pos h, if_pos (hiff.mpr h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mp hc))]
  have hrunA2' : StateT.run (runFunction (Avx512.fd_f25519_is_zero.denote
        (Ctxt.Valuation.singleton (.value ya)))) sA1
      = .value ([(PoisonOr.value (if Ref.readFieldElem? yr sR1.mem = some 0 then 1#32 else 0#32)
          : LLVM.IntW 32)]ₕ, sA2) := by
    rw [houtY]; exact hrunA2
  rw [BlockCom.run_bind_denote_call_cfg_of_value (c := Ref.fd_f25519_is_zero)
    (argTys := [SLLVM.Ty.ptr]) (argVals := (PoisonOr.value yr ::ₕ HVector.nil))
    (x := PoisonOr.value (if Ref.readFieldElem? yr sR1.mem = some 0 then 1#32 else 0#32))
    (s' := sR2) (by simp only [simp_spine, Ctxt.Valuation.singleton, hyrdef]) hrunR2]
  rw [BlockCom.run_bind_denote_call_cfg_of_value (c := Avx512.fd_f25519_is_zero)
    (argTys := [SLLVM.Ty.ptr]) (argVals := (PoisonOr.value ya ::ₕ HVector.nil))
    (x := PoisonOr.value (if Ref.readFieldElem? yr sR1.mem = some 0 then 1#32 else 0#32))
    (s' := sA2) (by simp only [simp_spine, Ctxt.Valuation.singleton, hyadef]) hrunA2']

  sorry


  -- Placeholder only. Delete once the ref walk is real: unification assigns
  -- `?r` and this goal disappears on its own.
  case r => sorry

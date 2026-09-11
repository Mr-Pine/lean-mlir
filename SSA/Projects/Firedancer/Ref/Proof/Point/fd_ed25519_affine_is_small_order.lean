/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Spec.Point.fd_ed25519_affine_is_small_order
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Proof.WriteChain
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Point
import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_point_to
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_is_zero
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_eq

/-!
# `fd_ed25519_affine_is_small_order` conformance (ref)

Five calls and three `or`s. The region copies the point into four fresh locals,
tests `x` and `y` for zero, compares `y` against each order-8 global, and `or`s
the four `i32`s.

The proof spends its length on transport, not on arithmetic. `fd_ed25519_point_to`
is the only callee that writes, and it writes only to the four allocas, so one
`FrameBelow` fact carries the argument and both globals from entry to return;
the locals themselves sit above the frame and are carried by each callee's own
equivalence. The four predicates are read back as values, and the last step is
`isSmallOrderTest_iff_mem`, which turns the disjunction the `or`s compute into
membership in `lowOrder`.

## Shape

`run_runFunction'` comes first, so the region's final state stays existential
while the walk runs, and each callee's state is obtained at the step that runs
it. Nothing before a call mentions the state after it.

## Why it elaborates in seconds

Three things, none of them guessable, and together the difference between ten
seconds and four minutes.

* Facts about the copy are transported with `live?_of_equiv_mem`, whose
  equivalence is stated over `{ s with mem := m }`, so the callee's write chain
  unifies whole. `hptstate_eq.live q` instead makes the elaborator walk a
  projection through four splices, at four seconds a use.
* `wf_splice4` and `frameBelow_splice4` (`Proof/WriteChain.lean`) state the write
  chain once, at the shape the callee's specification produces. The
  `FrameBelow.splice` tower proves the same thing but nests one structure update
  per store, and matching that against a single update is what costs the minutes.
* Those lemmas end on `rw` with no `show`. Spelling the goal out first
  re-elaborates the chain and costs five seconds on its own.

The AVX-512 twin, `Avx512/Proof/Point/fd_ed25519_affine_is_small_order.lean`, is
the same walk over `vector<8xi64>` slots and follows the same three rules.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

-- the callees are reached only through their conformance theorems; unfolding
-- them puts every callee's instructions into the stepper's defeq checks
attribute [local irreducible] fd_ed25519_point_to fd_f25519_is_zero fd_f25519_eq

set_option maxHeartbeats 400000 in
set_option maxRecDepth 40000 in
theorem fd_ed25519_affine_is_small_order_conforms (a : Pointer) (s : GlobalState)
    (ha : IsPointPtr s.mem a) :
    fd_ed25519_affine_is_small_order_spec a s ha := by
  simp only [fd_ed25519_affine_is_small_order_spec, Cfg.denote]
  intro hrefwf hZ hcurve haLimbs
  have hs : s.WF := hrefwf.wf

  -- the two order-8 globals, at whatever addresses the loader chose
  obtain ⟨g0, hgy0, -⟩ := hrefwf.gy0
  obtain ⟨g1, hgy1, -⟩ := hrefwf.gy1

  -- `fd_f25519_t x[1], y[1], z[1], t[1]`
  obtain ⟨xr, r1, hxrdef, hr1def, hr1, hxrfits, hxrid, hxroff, hctr1, -⟩ :=
    GlobalState.exists_afterAlloca_facts s hs (5 * 64)
  obtain ⟨yr, r2, hyrdef, hr2def, hr2, hyrfits, hyrid, hyroff, hctr2, hfr2⟩ :=
    GlobalState.exists_afterAlloca_facts r1 hr1 (5 * 64)
  obtain ⟨zr, r3, hzrdef, hr3def, hr3, hzrfits, hzrid, hzroff, hctr3, hfr3⟩ :=
    GlobalState.exists_afterAlloca_facts r2 hr2 (5 * 64)
  obtain ⟨tr, r4, htrdef, hr4def, hr4, htrfits, htrid, htroff, hctr4, hfr4⟩ :=
    GlobalState.exists_afterAlloca_facts r3 hr3 (5 * 64)

  -- the four locals sit at consecutive ids above the entry counter. Named
  -- here, where the context is still short: each is an `omega` over three
  -- equations, and every later frame step is one of them rather than a fresh
  -- search over the whole context.
  have hne : ∀ (q : Pointer) (b : BlockId),
      s.alloc.nextFreeBlock ≤ q.id.id → b.id < s.alloc.nextFreeBlock → q.id ≠ b :=
    fun q b hq hb h => by have := congrArg BlockId.id h; omega
  have hxrge : s.alloc.nextFreeBlock ≤ xr.id.id := by omega
  have hyrge : s.alloc.nextFreeBlock ≤ yr.id.id := by omega
  have hzrge : s.alloc.nextFreeBlock ≤ zr.id.id := by omega
  have htrge : s.alloc.nextFreeBlock ≤ tr.id.id := by omega
  have hxrlt1 : xr.id.id < r1.alloc.nextFreeBlock := by omega
  have hyrlt2 : yr.id.id < r2.alloc.nextFreeBlock := by omega
  have hzrlt3 : zr.id.id < r3.alloc.nextFreeBlock := by omega

  -- one frame fact per prefix: everything below `s`'s counter is untouched
  have fb1 : FrameBelow s.alloc.nextFreeBlock s r1 :=
    hr1def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
  have fb2 : FrameBelow s.alloc.nextFreeBlock s r2 :=
    hr2def ▸ FrameBelow.afterAlloca (by omega) fb1
  have fb3 : FrameBelow s.alloc.nextFreeBlock s r3 :=
    hr3def ▸ FrameBelow.afterAlloca (by omega) fb2
  have fb4 : FrameBelow s.alloc.nextFreeBlock s r4 :=
    hr4def ▸ FrameBelow.afterAlloca (by omega) fb3

  -- and the same for the frames each local was allocated in, so a local
  -- survives the allocas that follow it
  have fbr1 : FrameBelow r1.alloc.nextFreeBlock r1 r4 := by
    have h2 : FrameBelow r1.alloc.nextFreeBlock r1 r2 :=
      hr2def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
    have h3 : FrameBelow r1.alloc.nextFreeBlock r1 r3 :=
      hr3def ▸ FrameBelow.afterAlloca (by omega) h2
    exact hr4def ▸ FrameBelow.afterAlloca (by omega) h3
  have fbr2 : FrameBelow r2.alloc.nextFreeBlock r2 r4 := by
    have h3 : FrameBelow r2.alloc.nextFreeBlock r2 r3 :=
      hr3def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
    exact hr4def ▸ FrameBelow.afterAlloca (by omega) h3
  have fbr3 : FrameBelow r3.alloc.nextFreeBlock r3 r4 :=
    hr4def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)

  have hxr4 : IsFieldElemPtr r4.mem xr :=
    ⟨fits_of_live?_eq (fbr1 xr.id hxrlt1) hxrfits, by rw [hxroff]; simp⟩
  have hyr4 : IsFieldElemPtr r4.mem yr :=
    ⟨fits_of_live?_eq (fbr2 yr.id hyrlt2) hyrfits, by rw [hyroff]; simp⟩
  have hzr4 : IsFieldElemPtr r4.mem zr :=
    ⟨fits_of_live?_eq (fbr3 zr.id hzrlt3) hzrfits, by rw [hzroff]; simp⟩
  have htr4 : IsFieldElemPtr r4.mem tr := ⟨htrfits, by rw [htroff]; simp⟩

  -- the caller's pointers, transported to the state the copy runs in
  have hold : ∀ r : Pointer, IsFieldElemPtr s.mem r → r.id.id < s.alloc.nextFreeBlock :=
    fun r hr => lt_nextFreeBlock_of_fits hs hr.left
  have halt : a.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs ha.left
  have ha4 : IsPointPtr r4.mem a := isPointPtr_of_live?_eq (fb4 a.id halt) ha

  -- the four locals and `a` are pairwise distinct blocks: consecutive ids
  -- above a counter the argument predates
  have hNodup : ([xr, yr, zr, tr, a].map Pointer.id).Nodup := by
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or, List.nodup_nil, and_true]
    and_intros <;>
      first
        | exact fun h => absurd (congrArg BlockId.id h) (by omega)
        | exact id

  have hreadPt : readPoint ha4 = readPoint ha := readPoint_of_live?_eq (fb4 a.id halt) ha ha4

  -- the argument's per-coordinate bounds, at the state the copy runs in
  have haLimbs4 : AllLimbBounds ha4 := by
    intro i
    show LimbBounds (isCoordPtr ha4 i)
    refine limbBounds_of_readLimb? _ (fun k l hl => ?_)
    rw [readLimb?_of_live?_eq (p := a.withOffset (i * (5 * 8))) (fb4 a.id halt) k] at hl
    exact limbBounds_readLimb? (isCoordPtr ha i) (coordLimbBounds ha haLimbs i) k l hl

  -- Everything above is about the entry state and its four locals. The walk
  -- starts here; each callee's state is obtained where the walk reaches it, so
  -- no step carries a state it has not yet run.
  refine run_runFunction' (s ≈ ·) ?_

  -- `%0`: the `i32` 1
  denote_step_all v 0
  denote_eval v 0 0
  simp only [LLVM.const?] at hv0
  subst hv0

  -- `%1`, `%2`: the two `addressof`es
  peel_addressof hgy0.addr
  peel_addressof hgy1.addr

  -- `%3`--`%6`: `x, y, z, t`
  peel_alloca from s as r1 with hr1def
  peel_alloca from r1 as r2 with hr2def
  peel_alloca from r2 as r3 with hr3def
  peel_alloca from r3 as r4 with hr4def
  rw [← hxrdef, ← hyrdef, ← hzrdef, ← htrdef]
  peel_lifetime
  peel_lifetime
  peel_lifetime
  peel_lifetime

  -- `fd_ed25519_point_to( x, y, z, t, a )`
  obtain ⟨oX, oY, oZ, oT, ⟨ptstate, hptstate, hptstate_eq⟩, hlimbX, hlimbY, -, -,
      hvalX, hvalY, -, -⟩ :=
    fd_ed25519_point_to_conforms xr yr zr tr a r4 hr4 hNodup ha4 hxr4 hyr4 hzr4 htr4

  peel_call hptstate

  -- the copy's own witnesses, in this proof's terms rather than the spec's;
  -- `readLimb` ignores its proof argument, so the two are interchangeable
  have hoXm : IsFieldElemPtr
      ((((r4.mem.splice xr oX).splice yr oY).splice zr oZ).splice tr oT) xr :=
    isFieldElemPtr_splice (p := tr) (x := oT) (isFieldElemPtr_splice (p := zr) (x := oZ)
      (isFieldElemPtr_splice (p := yr) (x := oY)
        (isFieldElemPtr_splice (p := xr) (x := oX) hxr4)))
  have hoYm : IsFieldElemPtr
      ((((r4.mem.splice xr oX).splice yr oY).splice zr oZ).splice tr oT) yr :=
    isFieldElemPtr_splice (p := tr) (x := oT) (isFieldElemPtr_splice (p := zr) (x := oZ)
      (isFieldElemPtr_splice (p := yr) (x := oY)
        (isFieldElemPtr_splice (p := xr) (x := oX) hyr4)))
  have haXm : IsFieldElemPtr r4.mem a := coordPtr_zero a ▸ isCoordPtr ha4 0
  have haYm : IsFieldElemPtr r4.mem (a.withOffset 40) := coordPtr_one a ▸ isCoordPtr ha4 1

  have hXlimb : ∀ i, readLimb i hoXm = readLimb i haXm := hlimbX
  have hYlimb : ∀ i, readLimb i hoYm = readLimb i haYm := hlimbY
  have hXvalOut : readFieldElem hoXm = (readPoint ha4).X := hvalX
  have hYvalOut : readFieldElem hoYm = (readPoint ha4).Y := hvalY

  have haXbnd : LimbBounds haXm :=
    limbBounds_congr (coordPtr_zero a) (coordLimbBounds ha4 haLimbs4 0)
  have haYbnd : LimbBounds haYm :=
    limbBounds_congr (coordPtr_one a) (coordLimbBounds ha4 haLimbs4 1)

  -- ... transported across the callee's equivalence, to the state it left
  have hptWF : ptstate.WF := (wf_splice4 hr4).of_equiv hptstate_eq
  have hxPt : IsFieldElemPtr ptstate.mem xr :=
    isFieldElemPtr_of_live?_eq (live?_of_equiv_mem hptstate_eq.symm xr.id) hoXm
  have hyPt : IsFieldElemPtr ptstate.mem yr :=
    isFieldElemPtr_of_live?_eq (live?_of_equiv_mem hptstate_eq.symm yr.id) hoYm
  have hxPtBnd : LimbBounds hxPt := by
    intro i
    rw [readLimb_eq_of_readLimb? (h' := hoXm)
        (readLimb?_of_live?_eq (live?_of_equiv_mem hptstate_eq.symm xr.id) i),
      hXlimb i]
    exact haXbnd i
  have hyPtBnd : LimbBounds hyPt := by
    intro i
    rw [readLimb_eq_of_readLimb? (h' := hoYm)
        (readLimb?_of_live?_eq (live?_of_equiv_mem hptstate_eq.symm yr.id) i),
      hYlimb i]
    exact haYbnd i
  have hxPtVal : readFieldElem? xr ptstate.mem = some (readPoint ha).X :=
    (readFieldElem?_of_live?_eq (live?_of_equiv_mem hptstate_eq.symm xr.id)).trans
      ((Option.some_get (readFieldElem?_isSome hoXm)).symm.trans
        (congrArg some (hXvalOut.trans (congrArg Point.X hreadPt))))
  have hyPtVal : readFieldElem? yr ptstate.mem = some (readPoint ha).Y :=
    (readFieldElem?_of_live?_eq (live?_of_equiv_mem hptstate_eq.symm yr.id)).trans
      ((Option.some_get (readFieldElem?_isSome hoYm)).symm.trans
        (congrArg some (hYvalOut.trans (congrArg Point.Y hreadPt))))

  -- the frame across the copy: four stores, all to blocks above the counter
  have fbPt : FrameBelow s.alloc.nextFreeBlock s ptstate :=
    FrameBelow.of_equiv hptstate_eq (frameBelow_splice4 fb4 hxrge hyrge hzrge htrge)

  -- `fd_f25519_is_zero( x )`
  obtain ⟨izXstate, hizX, hizX_eq⟩ := fd_f25519_is_zero_conforms xr ptstate hptWF hxPt hxPtBnd
  peel_call hizX

  have hizXWF : izXstate.WF := hptWF.of_equiv hizX_eq
  have fbIzX : FrameBelow s.alloc.nextFreeBlock s izXstate := FrameBelow.of_equiv hizX_eq fbPt
  have hyIzX : IsFieldElemPtr izXstate.mem yr :=
    isFieldElemPtr_of_live?_eq (hizX_eq.live yr.id).symm hyPt
  have hyIzXBnd : LimbBounds hyIzX := by
    intro i
    rw [readLimb_eq_of_readLimb? (h' := hyPt) (readLimb?_of_live?_eq (hizX_eq.live yr.id).symm i)]
    exact hyPtBnd i
  have hyIzXVal : readFieldElem? yr izXstate.mem = some (readPoint ha).Y :=
    (readFieldElem?_of_live?_eq (hizX_eq.live yr.id).symm).trans hyPtVal

  -- `fd_f25519_is_zero( y )`
  obtain ⟨izYstate, hizY, hizY_eq⟩ := fd_f25519_is_zero_conforms yr izXstate hizXWF hyIzX hyIzXBnd
  peel_call hizY

  have hizYWF : izYstate.WF := hizXWF.of_equiv hizY_eq
  have fbIzY : FrameBelow s.alloc.nextFreeBlock s izYstate := FrameBelow.of_equiv hizY_eq fbIzX
  have hyIzY : IsFieldElemPtr izYstate.mem yr :=
    isFieldElemPtr_of_live?_eq (hizY_eq.live yr.id).symm hyIzX
  have hyIzYBnd : LimbBounds hyIzY := by
    intro i
    rw [readLimb_eq_of_readLimb? (h' := hyIzX) (readLimb?_of_live?_eq (hizY_eq.live yr.id).symm i)]
    exact hyIzXBnd i
  have hyIzYVal : readFieldElem? yr izYstate.mem = some (readPoint ha).Y :=
    (readFieldElem?_of_live?_eq (hizY_eq.live yr.id).symm).trans hyIzXVal

  -- the globals, at the state each comparison runs in
  have hg0IzY : IsFieldElemPtr izYstate.mem g0 :=
    isFieldElemPtr_of_live?_eq (fbIzY g0.id (hold g0 hgy0.ptr)) hgy0.ptr
  have hg0IzYBnd : LimbBounds hg0IzY := by
    intro i
    rw [readLimb_eq_of_readLimb? (h' := hgy0.ptr)
      (readLimb?_of_live?_eq (fbIzY g0.id (hold g0 hgy0.ptr)) i)]
    exact hgy0.bnd i
  have hg0IzYVal : readFieldElem? g0 izYstate.mem = some order8_y0 :=
    (readFieldElem?_of_live?_eq (fbIzY g0.id (hold g0 hgy0.ptr))).trans
      ((Option.some_get (readFieldElem?_isSome hgy0.ptr)).symm.trans (congrArg some hgy0.value))

  -- `%9 = or %8, %7`
  denote_step_all v 9
  denote_eval v 9 9
  simp only [LLVM.or, LLVM.or?] at hv9
  subst hv9

  -- `fd_f25519_eq( y, y0 )`
  obtain ⟨eq0state, heq0, heq0_eq⟩ :=
    fd_f25519_eq_conforms yr g0 izYstate hizYWF hyIzY hg0IzY hyIzYBnd (LimbBounds.bias hg0IzYBnd)
  peel_call heq0

  have heq0WF : eq0state.WF := hizYWF.of_equiv heq0_eq
  have fbEq0 : FrameBelow s.alloc.nextFreeBlock s eq0state := FrameBelow.of_equiv heq0_eq fbIzY
  have hyEq0 : IsFieldElemPtr eq0state.mem yr :=
    isFieldElemPtr_of_live?_eq (heq0_eq.live yr.id).symm hyIzY
  have hyEq0Bnd : LimbBounds hyEq0 := by
    intro i
    rw [readLimb_eq_of_readLimb? (h' := hyIzY) (readLimb?_of_live?_eq (heq0_eq.live yr.id).symm i)]
    exact hyIzYBnd i
  have hyEq0Val : readFieldElem? yr eq0state.mem = some (readPoint ha).Y :=
    (readFieldElem?_of_live?_eq (heq0_eq.live yr.id).symm).trans hyIzYVal
  have hg1Eq0 : IsFieldElemPtr eq0state.mem g1 :=
    isFieldElemPtr_of_live?_eq (fbEq0 g1.id (hold g1 hgy1.ptr)) hgy1.ptr
  have hg1Eq0Bnd : LimbBounds hg1Eq0 := by
    intro i
    rw [readLimb_eq_of_readLimb? (h' := hgy1.ptr)
      (readLimb?_of_live?_eq (fbEq0 g1.id (hold g1 hgy1.ptr)) i)]
    exact hgy1.bnd i
  have hg1Eq0Val : readFieldElem? g1 eq0state.mem = some order8_y1 :=
    (readFieldElem?_of_live?_eq (fbEq0 g1.id (hold g1 hgy1.ptr))).trans
      ((Option.some_get (readFieldElem?_isSome hgy1.ptr)).symm.trans (congrArg some hgy1.value))

  -- `%11 = or %9, %10`
  denote_step_all v 11
  denote_eval v 11 11
  simp only [LLVM.or, LLVM.or?] at hv11
  subst hv11

  -- `fd_f25519_eq( y, y1 )`
  obtain ⟨eq1state, heq1, heq1_eq⟩ :=
    fd_f25519_eq_conforms yr g1 eq0state heq0WF hyEq0 hg1Eq0 hyEq0Bnd (LimbBounds.bias hg1Eq0Bnd)
  peel_call heq1

  have fbEq1 : FrameBelow s.alloc.nextFreeBlock s eq1state := FrameBelow.of_equiv heq1_eq fbEq0

  -- the state the region returns in, and the frame it restores
  refine ⟨eq1state, ?_, GlobalState.Equiv.symm (FrameBelow.popFrame_equiv hs fbEq1)⟩

  -- `%13 = or %11, %12`
  denote_step_all v 13
  denote_eval v 13 13
  simp only [LLVM.or, LLVM.or?] at hv13
  subst hv13

  peel_lifetime
  peel_lifetime
  peel_lifetime
  peel_lifetime
  simp_return

  -- what the four predicates actually compared
  rw [hxPtVal, hyIzXVal, readFieldElem_eq_of hyIzYVal, readFieldElem_eq_of hg0IzYVal,
    readFieldElem_eq_of hyEq0Val, readFieldElem_eq_of hg1Eq0Val]

  -- and what their disjunction decides
  simp only [Option.some.injEq, or_ite_or]
  refine if_congr ?_ rfl rfl
  rw [← isSmallOrderTest_iff_mem (P := readPoint ha) hZ hcurve]
  simp only [IsSmallOrderTest]
  constructor
  · rintro (((h | h) | h) | h)
    exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr (Or.inl h)),
      Or.inr (Or.inr (Or.inr h))]
  · rintro (h | h | h | h)
    exacts [Or.inl (Or.inl (Or.inr h)), Or.inl (Or.inl (Or.inl h)), Or.inl (Or.inr h), Or.inr h]

end Firedancer.Ref

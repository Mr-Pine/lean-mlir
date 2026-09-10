/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_affine_is_small_order
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Proof.WriteChain
import SSA.Projects.Firedancer.Avx512.Proof.Step.Basic
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_to
import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_f25519_is_zero
import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_f25519_eq

/-!
# `fd_ed25519_affine_is_small_order` conformance (AVX-512)

The ref proof's twin, step for step: the two regions come from the same source
and differ only in the field representation, so this one differs only in reading
`vector<8xi64>` slots where that one reads five-limb ones.

`run_runFunction'` comes first and each callee's state is obtained where the walk
reaches it. `fd_ed25519_point_to` is the only callee that writes, and only to the
four allocas, so `frameBelow_splice4` carries the argument and both globals from
entry to return; the locals ride each callee's own equivalence.

Reducedness is per slot, as the specification states it: `point_to` writes `x` as
`widenVec` of the QUAD's `X` vector, so `Reduced (widenVec …)` is what the
`fd_f25519_is_zero` and `fd_f25519_eq` calls consume, and the two high lanes are
clear by construction.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

-- the callees are reached only through their conformance theorems
attribute [local irreducible] fd_ed25519_point_to fd_f25519_is_zero fd_f25519_eq

set_option maxHeartbeats 400000 in
set_option maxRecDepth 40000 in
theorem fd_ed25519_affine_is_small_order_conforms (a g0 g1 : Pointer) (s : GlobalState)
    (hs : s.WF) (ha : IsQuadPtr s.mem a)
    (hg0 : IsVecPtr s.mem g0) (hg1 : IsVecPtr s.mem g1) :
    fd_ed25519_affine_is_small_order_spec a g0 g1 s ha hg0 hg1 := by
  simp only [fd_ed25519_affine_is_small_order_spec, Cfg.denote]
  intro hZ hcurve hgp0 hgp1 hgval0 hgval1 hgred0 hgred1 hredX hredY

  -- `fd_f25519_t x[1], y[1], z[1], t[1]`, 64 bytes each
  obtain ⟨xa, r1, hxadef, hr1def, hr1, hxafits, hxaid, hxaoff, hctr1, -⟩ :=
    GlobalState.exists_afterAlloca_facts s hs (8 * 64)
  obtain ⟨ya, r2, hyadef, hr2def, hr2, hyafits, hyaid, hyaoff, hctr2, -⟩ :=
    GlobalState.exists_afterAlloca_facts r1 hr1 (8 * 64)
  obtain ⟨za, r3, hzadef, hr3def, hr3, hzafits, hzaid, hzaoff, hctr3, -⟩ :=
    GlobalState.exists_afterAlloca_facts r2 hr2 (8 * 64)
  obtain ⟨ta, r4, htadef, hr4def, hr4, htafits, htaid, htaoff, hctr4, -⟩ :=
    GlobalState.exists_afterAlloca_facts r3 hr3 (8 * 64)

  -- the block-id arithmetic, named while the context is short
  have hxage : s.alloc.nextFreeBlock ≤ xa.id.id := by omega
  have hyage : s.alloc.nextFreeBlock ≤ ya.id.id := by omega
  have hzage : s.alloc.nextFreeBlock ≤ za.id.id := by omega
  have htage : s.alloc.nextFreeBlock ≤ ta.id.id := by omega
  have hxalt1 : xa.id.id < r1.alloc.nextFreeBlock := by omega
  have hyalt2 : ya.id.id < r2.alloc.nextFreeBlock := by omega
  have hzalt3 : za.id.id < r3.alloc.nextFreeBlock := by omega

  have fb1 : FrameBelow s.alloc.nextFreeBlock s r1 :=
    hr1def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
  have fb2 : FrameBelow s.alloc.nextFreeBlock s r2 :=
    hr2def ▸ FrameBelow.afterAlloca (by omega) fb1
  have fb3 : FrameBelow s.alloc.nextFreeBlock s r3 :=
    hr3def ▸ FrameBelow.afterAlloca (by omega) fb2
  have fb4 : FrameBelow s.alloc.nextFreeBlock s r4 :=
    hr4def ▸ FrameBelow.afterAlloca (by omega) fb3
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

  have hxa4 : IsVecPtr r4.mem xa :=
    ⟨fits_of_live?_eq (fbr1 xa.id hxalt1) hxafits, by rw [hxaoff]; simp⟩
  have hya4 : IsVecPtr r4.mem ya :=
    ⟨fits_of_live?_eq (fbr2 ya.id hyalt2) hyafits, by rw [hyaoff]; simp⟩
  have hza4 : IsVecPtr r4.mem za :=
    ⟨fits_of_live?_eq (fbr3 za.id hzalt3) hzafits, by rw [hzaoff]; simp⟩
  have hta4 : IsVecPtr r4.mem ta := ⟨htafits, by rw [htaoff]; simp⟩

  have hg0lt : g0.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hg0.1
  have hg1lt : g1.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hg1.1
  have halt : a.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs ha.1
  have ha4 : IsQuadPtr r4.mem a := ⟨fits_of_live?_eq (fb4 a.id halt) ha.1, ha.2⟩
  have hq4 : readQuad ha4 = readQuad ha := readQuad_of_live?_eq (fb4 a.id halt) ha ha4

  have hNodup : ([xa, ya, za, ta].map Pointer.id).Nodup := by
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or, List.nodup_nil, and_true]
    and_intros <;>
      first
        | exact fun h => absurd (congrArg BlockId.id h) (by omega)
        | exact id

  -- the argument's reducedness, at the state the copy runs in
  have hredX4 : R43x6.Reduced (widenVec (readQuad ha4).PointVecs.X) := by rw [hq4]; exact hredX
  have hredY4 : R43x6.Reduced (widenVec (readQuad ha4).PointVecs.Y) := by rw [hq4]; exact hredY

  -- The walk starts here; each callee's state is obtained where it is reached.
  refine run_runFunction' (s ≈ ·) ?_

  -- `%0`--`%5`: the `i32` 1 and the first global's dead initialiser chain
  denote_step_all v 5
  denote_eval v 0 0
  simp only [LLVM.const?] at hv0
  subst hv0

  -- `%6`, `%12`: the two `addressof`es, with `%7`--`%11` between them
  peel_addressof hgp0
  denote_step_all v 11
  peel_addressof hgp1

  -- `%13`--`%16`: `x, y, z, t`
  peel_alloca from s as r1 with hr1def
  peel_alloca from r1 as r2 with hr2def
  peel_alloca from r2 as r3 with hr3def
  peel_alloca from r3 as r4 with hr4def
  rw [← hxadef, ← hyadef, ← hzadef, ← htadef]
  peel_lifetime
  peel_lifetime
  peel_lifetime
  peel_lifetime

  -- `fd_ed25519_point_to( x, y, z, t, a )`
  obtain ⟨⟨ptstate, hptstate, hptstate_eq⟩, hrX, hrY, -, -, hvX, hvY, -, -⟩ :=
    fd_ed25519_point_to_conforms xa ya za ta a r4 hr4 hNodup ha4 hxa4 hya4 hza4 hta4
  peel_call hptstate

  -- the two slots the region reads back, in this proof's terms
  have hoXm := isVecPtr_splice (q := ta) (x := vecBV (widenVec (readQuad ha4).PointVecs.T))
    (isVecPtr_splice (q := za) (x := vecBV (widenVec (readQuad ha4).PointVecs.Z))
      (isVecPtr_splice (q := ya) (x := vecBV (widenVec (readQuad ha4).PointVecs.Y))
        (isVecPtr_splice (q := xa) (x := vecBV (widenVec (readQuad ha4).PointVecs.X)) hxa4)))
  have hoYm := isVecPtr_splice (q := ta) (x := vecBV (widenVec (readQuad ha4).PointVecs.T))
    (isVecPtr_splice (q := za) (x := vecBV (widenVec (readQuad ha4).PointVecs.Z))
      (isVecPtr_splice (q := ya) (x := vecBV (widenVec (readQuad ha4).PointVecs.Y))
        (isVecPtr_splice (q := xa) (x := vecBV (widenVec (readQuad ha4).PointVecs.X)) hya4)))

  have hptWF : ptstate.WF := (wf_splice4 hr4).of_equiv hptstate_eq
  have fbPt : FrameBelow s.alloc.nextFreeBlock s ptstate :=
    FrameBelow.of_equiv hptstate_eq (frameBelow_splice4 fb4 hxage hyage hzage htage)

  -- The two slots, transported to the state the copy left. Both facts go
  -- through `live?_of_equiv_mem'`, whose equation already has the write chain
  -- on the right: `isVecPtr_of_equiv`/`readVec_of_equiv` take whole states, so
  -- each use would project `.mem` through four splices instead.
  have hxLive := live?_of_equiv_mem' hptstate_eq.symm xa.id
  have hyLive := live?_of_equiv_mem' hptstate_eq.symm ya.id
  have hxPt : IsVecPtr ptstate.mem xa := ⟨fits_of_live?_eq hxLive hoXm.1, hoXm.2⟩
  have hyPt : IsVecPtr ptstate.mem ya := ⟨fits_of_live?_eq hyLive hoYm.1, hoYm.2⟩
  have hxPtRead0 : readVec hxPt = readVec hoXm := by
    simp only [readVec, readVec?_of_live?_eq hxLive]
  have hyPtRead0 : readVec hyPt = readVec hoYm := by
    simp only [readVec, readVec?_of_live?_eq hyLive]
  have hxPtRead : readVec hxPt = widenVec (readQuad ha4).PointVecs.X := hxPtRead0.trans hrX
  have hyPtRead : readVec hyPt = widenVec (readQuad ha4).PointVecs.Y := hyPtRead0.trans hrY
  have hxPtVal : vecValue (readVec hxPt) = (readQuad ha).toPoint.X :=
    ((congrArg vecValue hxPtRead0).trans hvX).trans (congrArg (fun w => w.toPoint.X) hq4)
  have hyPtVal : vecValue (readVec hyPt) = (readQuad ha).toPoint.Y :=
    ((congrArg vecValue hyPtRead0).trans hvY).trans (congrArg (fun w => w.toPoint.Y) hq4)

  -- `fd_f25519_is_zero( x )`
  obtain ⟨izXstate, hizX, hizX_eq⟩ :=
    fd_f25519_is_zero_conforms xa ptstate hptWF hxPt
      (by rw [hxPtRead]; exact hredX4.nearlyReduced)
      (by rw [hxPtRead]; rfl) (by rw [hxPtRead]; rfl)
  peel_call hizX

  have hizXWF : izXstate.WF := hptWF.of_equiv hizX_eq
  have fbIzX : FrameBelow s.alloc.nextFreeBlock s izXstate := FrameBelow.of_equiv hizX_eq fbPt
  have hyIzX : IsVecPtr izXstate.mem ya := isVecPtr_of_equiv hizX_eq hyPt
  have hyIzXRead : readVec hyIzX = widenVec (readQuad ha4).PointVecs.Y :=
    (readVec_of_equiv hizX_eq hyPt).trans hyPtRead
  have hyIzXVal : vecValue (readVec hyIzX) = (readQuad ha).toPoint.Y :=
    (congrArg vecValue (readVec_of_equiv hizX_eq hyPt)).trans hyPtVal

  -- `fd_f25519_is_zero( y )`
  obtain ⟨izYstate, hizY, hizY_eq⟩ :=
    fd_f25519_is_zero_conforms ya izXstate hizXWF hyIzX
      (by rw [hyIzXRead]; exact hredY4.nearlyReduced)
      (by rw [hyIzXRead]; rfl) (by rw [hyIzXRead]; rfl)
  peel_call hizY

  have hizYWF : izYstate.WF := hizXWF.of_equiv hizY_eq
  have fbIzY : FrameBelow s.alloc.nextFreeBlock s izYstate := FrameBelow.of_equiv hizY_eq fbIzX
  have hyIzY : IsVecPtr izYstate.mem ya := isVecPtr_of_equiv hizY_eq hyIzX
  have hyIzYRead : readVec hyIzY = widenVec (readQuad ha4).PointVecs.Y :=
    (readVec_of_equiv hizY_eq hyIzX).trans hyIzXRead
  have hyIzYVal : vecValue (readVec hyIzY) = (readQuad ha).toPoint.Y :=
    (congrArg vecValue (readVec_of_equiv hizY_eq hyIzX)).trans hyIzXVal

  -- the first global, at the state the comparison runs in
  have hg0IzY : IsVecPtr izYstate.mem g0 :=
    ⟨fits_of_live?_eq (fbIzY g0.id hg0lt) hg0.1, hg0.2⟩
  have hg0IzYRead : readVec hg0IzY = readVec hg0 := by
    simp only [readVec, readVec?_of_live?_eq (fbIzY g0.id hg0lt)]

  -- `%19 = or %18, %17`
  denote_step_all v 19
  denote_eval v 19 19
  simp only [LLVM.or, LLVM.or?] at hv19
  subst hv19

  -- `fd_f25519_eq( y, y0 )`
  obtain ⟨eq0state, heq0, heq0_eq⟩ :=
    fd_f25519_eq_conforms ya g0 izYstate hizYWF hyIzY hg0IzY
      (by rw [hyIzYRead]; exact hredY4) (by rw [hg0IzYRead]; exact hgred0)
  peel_call heq0

  have heq0WF : eq0state.WF := hizYWF.of_equiv heq0_eq
  have fbEq0 : FrameBelow s.alloc.nextFreeBlock s eq0state := FrameBelow.of_equiv heq0_eq fbIzY
  have hyEq0 : IsVecPtr eq0state.mem ya := isVecPtr_of_equiv heq0_eq hyIzY
  have hyEq0Read : readVec hyEq0 = widenVec (readQuad ha4).PointVecs.Y :=
    (readVec_of_equiv heq0_eq hyIzY).trans hyIzYRead
  have hyEq0Val : vecValue (readVec hyEq0) = (readQuad ha).toPoint.Y :=
    (congrArg vecValue (readVec_of_equiv heq0_eq hyIzY)).trans hyIzYVal
  have hg1Eq0 : IsVecPtr eq0state.mem g1 :=
    ⟨fits_of_live?_eq (fbEq0 g1.id hg1lt) hg1.1, hg1.2⟩
  have hg1Eq0Read : readVec hg1Eq0 = readVec hg1 := by
    simp only [readVec, readVec?_of_live?_eq (fbEq0 g1.id hg1lt)]

  -- `%21 = or %19, %20`
  denote_step_all v 21
  denote_eval v 21 21
  simp only [LLVM.or, LLVM.or?] at hv21
  subst hv21

  -- `fd_f25519_eq( y, y1 )`
  obtain ⟨eq1state, heq1, heq1_eq⟩ :=
    fd_f25519_eq_conforms ya g1 eq0state heq0WF hyEq0 hg1Eq0
      (by rw [hyEq0Read]; exact hredY4) (by rw [hg1Eq0Read]; exact hgred1)
  peel_call heq1

  have fbEq1 : FrameBelow s.alloc.nextFreeBlock s eq1state := FrameBelow.of_equiv heq1_eq fbEq0

  -- the state the region returns in, and the frame it restores
  refine ⟨eq1state, ?_, GlobalState.Equiv.symm (FrameBelow.popFrame_equiv hs fbEq1)⟩

  -- `%23 = or %21, %22`
  denote_step_all v 23
  denote_eval v 23 23
  simp only [LLVM.or, LLVM.or?] at hv23
  subst hv23

  peel_lifetime
  peel_lifetime
  peel_lifetime
  peel_lifetime
  simp_return

  -- what the four predicates actually compared
  rw [hxPtVal, hyIzXVal, hyIzYVal, hyEq0Val, congrArg vecValue hg0IzYRead,
    congrArg vecValue hg1Eq0Read, hgval0, hgval1]

  -- and what their disjunction decides
  simp only [or_ite_or]
  refine if_congr ?_ rfl rfl
  rw [← isSmallOrderTest_iff_mem (P := (readQuad ha).toPoint) hZ hcurve]
  simp only [IsSmallOrderTest]
  constructor
  · rintro (((h | h) | h) | h)
    exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr (Or.inl h)),
      Or.inr (Or.inr (Or.inr h))]
  · rintro (h | h | h | h)
    exacts [Or.inl (Or.inl (Or.inr h)), Or.inl (Or.inl (Or.inl h)), Or.inl (Or.inr h), Or.inr h]

end Firedancer.Avx512

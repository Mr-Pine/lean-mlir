import SSA.Projects.Firedancer.Ref.Spec.Point.fd_ed25519_point_eq_z1
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_eq_z1
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Point

import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_mul
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_eq

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

-- the callees are used only through their conformance theorems, and unfolding
-- them means unfolding `fiat_25519_carry_mul`'s 125 instructions into every
-- defeq check the stepper makes
attribute [local irreducible] fd_f25519_mul fd_f25519_eq

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
theorem fd_ed25519_point_eq_z1_conforms (a b : Pointer) (s : GlobalState)
    (hs : s.WF)
    (ha : IsPointPtr s.mem a)
    (hb : IsPointPtr s.mem b)
    (haLimbs : AllLimbBounds ha)
    (hbLimbs : AllLimbBounds hb)
    (haZUnit : IsUnit (readPoint ha).Z) :
    fd_ed25519_point_eq_z1_spec a b s ha hb := by
  intro hz1
  simp only [Cfg.denote]

  -- the coordinates the region geps, at the byte offsets it computes. Field 0
  -- gets no gep, so `a` and `b` are themselves `a->X` and `b->X`.
  have paZ : IsFieldElemPtr s.mem (a.withOffset 120) := isCoordPtr a ha 3
  have paY : IsFieldElemPtr s.mem (a.withOffset 40) := isCoordPtr a ha 1
  have pbY : IsFieldElemPtr s.mem (b.withOffset 40) := isCoordPtr b hb 1
  have paX : IsFieldElemPtr s.mem a := coordPtr_zero a ▸ isCoordPtr a ha 0
  have pbX : IsFieldElemPtr s.mem b := coordPtr_zero b ▸ isCoordPtr b hb 0

  -- the input bounds, in the `readLimb?` form the callees take
  have baZ := limbBounds_readLimb? (isCoordPtr a ha 3) (coordLimbBounds ha haLimbs 3)
  have baY := limbBounds_readLimb? (isCoordPtr a ha 1) (coordLimbBounds ha haLimbs 1)
  have bbY := limbBounds_readLimb? (isCoordPtr b hb 1) (coordLimbBounds hb hbLimbs 1)
  have baX : ∀ (i : Fin 5) (l : ℕ), readLimb? a i s.mem = some l → l ≤ 2 ^ 51 :=
    coordPtr_zero a ▸ limbBounds_readLimb? (isCoordPtr a ha 0) (coordLimbBounds ha haLimbs 0)
  have bbX : ∀ (i : Fin 5) (l : ℕ), readLimb? b i s.mem = some l → l ≤ 2 ^ 51 :=
    coordPtr_zero b ▸ limbBounds_readLimb? (isCoordPtr b hb 0) (coordLimbBounds hb hbLimbs 0)

  -- `fd_f25519_t x1[1], y1[1]`
  obtain ⟨x1, s₁, hx1def, hs₁def⟩ := GlobalState.exists_afterAlloca s (5 * 64)
  obtain ⟨y1, s₂, hy1def, hs₂def⟩ := GlobalState.exists_afterAlloca s₁ (5 * 64)

  have hs₁ : s₁.WF := hs₁def ▸ hs.afterAlloca _
  have hs₂ : s₂.WF := hs₂def ▸ hs₁.afterAlloca _

  have hx1id : x1.id.id = s.alloc.nextFreeBlock := by rw [hx1def]
  have hy1id : y1.id.id = s.alloc.nextFreeBlock + 1 := by rw [hy1def, hs₁def]; rfl

  -- a block that predates the frame is neither temporary, and neither `alloca`
  -- disturbs it
  have hnex : ∀ r : BlockId, r.id < s.alloc.nextFreeBlock → r ≠ x1.id := by
    intro r hr h; rw [h, hx1id] at hr; omega
  have hney : ∀ r : BlockId, r.id < s.alloc.nextFreeBlock → r ≠ y1.id := by
    intro r hr h; rw [h, hy1id] at hr; omega
  have hxy : y1.id ≠ x1.id := by intro h; rw [h, hx1id] at hy1id; omega
  have hlive₂ : ∀ r : BlockId, r.id < s.alloc.nextFreeBlock →
      s₂.mem.live? r = s.mem.live? r := by
    intro r hr
    subst hs₁def hs₂def
    exact (live?_afterAlloca_of_lt (by simp only [GlobalState.afterAlloca]; omega)).trans
      (live?_afterAlloca_of_lt hr)

  -- the pointer-shaped form the callee obligations take
  have hold : ∀ r : Pointer, IsFieldElemPtr s.mem r → r.id.id < s.alloc.nextFreeBlock :=
    fun r hr => lt_nextFreeBlock_of_fits hs hr.left
  have hS₂ : ∀ r : Pointer, IsFieldElemPtr s.mem r → s₂.mem.live? r.id = s.mem.live? r.id :=
    fun r hr => hlive₂ r.id (hold r hr)

  have px1₂ : IsFieldElemPtr s₂.mem x1 := by
    subst hx1def hs₁def hs₂def
    exact isFieldElemPtr_of_live?_eq
      (live?_afterAlloca_of_lt (by simp [GlobalState.afterAlloca]))
      (isFieldElemPtr_afterAlloca_self s)
  have py1₂ : IsFieldElemPtr s₂.mem y1 := by
    subst hy1def hs₂def; exact isFieldElemPtr_afterAlloca_self s₁

  -- `fd_f25519_mul( x1, b->X, a->Z )`
  obtain ⟨x1bits, hx1bits, ⟨x1state, hx1state, hx1state_eq⟩, bx1⟩ :=
    fd_f25519_mul_conforms x1 b (a.withOffset 120) s₂ hs₂ px1₂
      (isFieldElemPtr_of_live?_eq (hS₂ b pbX) pbX)
      (isFieldElemPtr_of_live?_eq (hS₂ _ paZ) paZ)
      (limbBounds_of_live?_eq (hS₂ b pbX) (fun i l h => (bbX i l h).trans (by norm_num)))
      (limbBounds_of_live?_eq (hS₂ _ paZ) (fun i l h => (baZ i l h).trans (by norm_num)))

  -- the mul writes only `x1`; every other block reads as it did in `s₂`
  have hlivex1 : ∀ r : BlockId, r ≠ x1.id → x1state.mem.live? r = s₂.mem.live? r :=
    fun r hr => (hx1state_eq.2 r).symm.trans (live?_splice_ne (Ne.symm hr))
  have hX : ∀ r : Pointer, IsFieldElemPtr s.mem r → x1state.mem.live? r.id = s.mem.live? r.id :=
    fun r hr => (hlivex1 r.id (hnex r.id (hold r hr))).trans (hS₂ r hr)
  have hx1WF : x1state.WF := GlobalState.WF.of_equiv hs₂.splice hx1state_eq
  have px1X : IsFieldElemPtr x1state.mem x1 :=
    isFieldElemPtr_of_live?_eq (hx1state_eq.2 x1.id).symm ⟨fits_splice px1₂.left, px1₂.right⟩
  have bx1X : ∀ (i : Fin 5) (l : ℕ), readLimb? x1 i x1state.mem = some l → l ≤ 2 ^ 51 :=
    limbBounds_of_live?_eq (m := (s₂.mem.splice x1 x1bits)) (hx1state_eq.2 x1.id).symm
      (fun i l h => (bx1 i l h).trans (by norm_num))
  have py1X : IsFieldElemPtr x1state.mem y1 :=
    isFieldElemPtr_of_live?_eq (hlivex1 y1.id hxy) py1₂

  -- `fd_f25519_mul( y1, b->Y, a->Z )`
  obtain ⟨y1bits, hy1bits, ⟨y1state, hy1state, hy1state_eq⟩, by1⟩ :=
    fd_f25519_mul_conforms y1 (b.withOffset 40) (a.withOffset 120) x1state hx1WF py1X
      (isFieldElemPtr_of_live?_eq (hX _ pbY) pbY)
      (isFieldElemPtr_of_live?_eq (hX _ paZ) paZ)
      (limbBounds_of_live?_eq (hX _ pbY) (fun i l h => (bbY i l h).trans (by norm_num)))
      (limbBounds_of_live?_eq (hX _ paZ) (fun i l h => (baZ i l h).trans (by norm_num)))

  have hlivey1 : ∀ r : BlockId, r ≠ y1.id → y1state.mem.live? r = x1state.mem.live? r :=
    fun r hr => (hy1state_eq.2 r).symm.trans (live?_splice_ne (Ne.symm hr))
  have hY : ∀ r : Pointer, IsFieldElemPtr s.mem r → y1state.mem.live? r.id = s.mem.live? r.id :=
    fun r hr => (hlivey1 r.id (hney r.id (hold r hr))).trans (hX r hr)
  have hy1WF : y1state.WF := GlobalState.WF.of_equiv hx1WF.splice hy1state_eq
  have py1Y : IsFieldElemPtr y1state.mem y1 :=
    isFieldElemPtr_of_live?_eq (hy1state_eq.2 y1.id).symm ⟨fits_splice py1X.left, py1X.right⟩
  have by1Y : ∀ (i : Fin 5) (l : ℕ), readLimb? y1 i y1state.mem = some l → l ≤ 2 ^ 51 :=
    limbBounds_of_live?_eq (m := (x1state.mem.splice y1 y1bits)) (hy1state_eq.2 y1.id).symm
      (fun i l h => (by1 i l h).trans (by norm_num))
  have px1Y : IsFieldElemPtr y1state.mem x1 :=
    isFieldElemPtr_of_live?_eq (hlivey1 x1.id (Ne.symm hxy)) px1X
  have paXY : IsFieldElemPtr y1state.mem a := isFieldElemPtr_of_live?_eq (hY a paX) paX

  -- `fd_f25519_eq( x1, a->X )`
  obtain ⟨eqx1state, heqx1state, heqx1state_eq⟩ :=
    fd_f25519_eq_conforms x1 a y1state hy1WF px1Y paXY
      (limbBounds_of_readLimb? px1Y (limbBounds_of_live?_eq (hlivey1 x1.id (Ne.symm hxy)) bx1X))
      (limbBounds_of_readLimb? paXY (limbBounds_of_live?_eq (hY a paX) baX))

  have hE : ∀ r : Pointer, IsFieldElemPtr s.mem r → eqx1state.mem.live? r.id = s.mem.live? r.id :=
    fun r hr => (heqx1state_eq.2 r.id).symm.trans (hY r hr)
  have heqx1WF : eqx1state.WF := GlobalState.WF.of_equiv hy1WF heqx1state_eq
  have py1E : IsFieldElemPtr eqx1state.mem y1 :=
    isFieldElemPtr_of_live?_eq (heqx1state_eq.2 y1.id).symm py1Y
  have paYE : IsFieldElemPtr eqx1state.mem (a.withOffset 40) :=
    isFieldElemPtr_of_live?_eq (hE _ paY) paY

  -- `fd_f25519_eq( y1, a->Y )`
  obtain ⟨eqy1state, heqy1state, heqy1state_eq⟩ :=
    fd_f25519_eq_conforms y1 (a.withOffset 40) eqx1state heqx1WF py1E paYE
      (limbBounds_of_readLimb? py1E
        (limbBounds_of_live?_eq (heqx1state_eq.2 y1.id).symm by1Y))
      (limbBounds_of_readLimb? paYE (limbBounds_of_live?_eq (hE _ paY) baY))

  -- the region's frame holds only `x1` and `y1`, so popping it restores `s`
  have hframe : ∀ r : BlockId, r.id < s.alloc.nextFreeBlock →
      eqy1state.mem.live? r = s.mem.live? r := by
    intro r hr
    rw [← heqy1state_eq.2 r, ← heqx1state_eq.2 r, hlivey1 r (hney r hr),
      hlivex1 r (hnex r hr), hlive₂ r hr]

  refine ⟨s.popFrame eqy1state.mem, ?_,
    GlobalState.Equiv.symm (GlobalState.killFrom_equiv eqy1state.mem hs hframe)⟩

  refine run_runFunction (s' := eqy1state) ?_

  denote_step_all v 2
  denote_eval v 0 2
  simp only [LLVM.const?] at hv0 hv1 hv2
  subst hv0 hv1 hv2

  peel_alloca from s as s₁ with hs₁def
  peel_alloca from s₁ as s₂ with hs₂def
  -- `peel_alloca` leaves the fresh pointers expanded; the callee equations name
  -- them `x1` and `y1`
  rw [← hx1def, ← hy1def]
  peel_lifetime
  peel_lifetime

  have haFits₂ : Fits s₂.mem a (4 * 5 * 64) :=
    fits_of_live?_eq (hlive₂ a.id (lt_nextFreeBlock_of_fits hs ha.1)) ha.1
  peel_gep 120 with a, haFits₂, s₂ as aZ

  peel_call hx1state

  have hbFitsX : Fits x1state.mem b (4 * 5 * 64) := fits_of_live?_eq (hX b pbX) hb.1
  peel_gep 40 with b, hbFitsX, x1state as bY
  peel_call hy1state
  peel_call heqx1state

  have haFitsE : Fits eqx1state.mem a (4 * 5 * 64) := fits_of_live?_eq (hE a paX) ha.1
  peel_gep 40 with a, haFitsE, eqx1state as aY
  peel_call heqy1state

  -- `%12 = and %11, %9`, the two lifetime ends, and the return
  denote_step_all v 12
  eval_llvm 12
  peel_lifetime
  peel_lifetime
  simp_return

  -- what each comparison actually reads: `x1` holds `b->X * a->Z` and `y1`
  -- holds `b->Y * a->Z`, against `a->X` and `a->Y` unchanged since `s`
  obtain ⟨haXval, haYval, haZval⟩ := readPoint_coords ha
  obtain ⟨hbXval, hbYval, hbZval⟩ := readPoint_coords hb

  have hx1read : readFieldElem? x1 y1state.mem = some ((readPoint hb).X * (readPoint ha).Z) := by
    rw [readFieldElem?_of_live?_eq (hlivey1 x1.id (Ne.symm hxy)),
      ← readFieldElem?_of_equiv hx1state_eq x1, readFieldElem?_splice x1bits px1₂.left, hx1bits,
      readFieldElem_eq_of ((readFieldElem?_of_live?_eq (hS₂ b pbX)).trans hbXval),
      readFieldElem_eq_of ((readFieldElem?_of_live?_eq (hS₂ _ paZ)).trans haZval)]
  have hy1read : readFieldElem? y1 eqx1state.mem = some ((readPoint hb).Y * (readPoint ha).Z) := by
    rw [readFieldElem?_of_live?_eq (heqx1state_eq.2 y1.id).symm,
      ← readFieldElem?_of_equiv hy1state_eq y1, readFieldElem?_splice y1bits py1X.left, hy1bits,
      readFieldElem_eq_of ((readFieldElem?_of_live?_eq (hX _ pbY)).trans hbYval),
      readFieldElem_eq_of ((readFieldElem?_of_live?_eq (hX _ paZ)).trans haZval)]
  have haXread : readFieldElem? a y1state.mem = some (readPoint ha).X :=
    (readFieldElem?_of_live?_eq (hY a paX)).trans haXval
  have haYread : readFieldElem? (a.withOffset 40) eqx1state.mem = some (readPoint ha).Y :=
    (readFieldElem?_of_live?_eq (hE _ paY)).trans haYval

  -- with `b->Z = 1` the two cross-products are exactly what `SamePoint` asks for
  have hsame : (readPoint ha).SamePoint (readPoint hb)
      ↔ ((readPoint hb).Y * (readPoint ha).Z = (readPoint ha).Y
        ∧ (readPoint hb).X * (readPoint ha).Z = (readPoint ha).X) := by
    rw [Point.samePoint_iff_cross haZUnit (by rw [hz1]; exact isUnit_one), hz1]
    simp only [mul_one]
    exact ⟨fun h => ⟨h.2.symm, h.1.symm⟩, fun h => ⟨h.2.symm, h.1.symm⟩⟩

  rw [hv12, hx1read, hy1read, haXread, haYread]
  simp only [Option.some.injEq]
  by_cases hA : (readPoint hb).Y * (readPoint ha).Z = (readPoint ha).Y <;>
    by_cases hB : (readPoint hb).X * (readPoint ha).Z = (readPoint ha).X
  · rw [if_pos hA, if_pos hB, if_pos (hsame.mpr ⟨hA, hB⟩)]; rfl
  · rw [if_pos hA, if_neg hB, if_neg fun h => hB (hsame.mp h).2]; rfl
  · rw [if_neg hA, if_pos hB, if_neg fun h => hA (hsame.mp h).1]; rfl
  · rw [if_neg hA, if_neg hB, if_neg fun h => hA (hsame.mp h).1]; rfl

end Firedancer.Ref

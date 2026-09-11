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
  have paZ : IsFieldElemPtr s.mem (a.withOffset 120) := isCoordPtr ha 3
  have paY : IsFieldElemPtr s.mem (a.withOffset 40) := isCoordPtr ha 1
  have pbY : IsFieldElemPtr s.mem (b.withOffset 40) := isCoordPtr hb 1
  have paX : IsFieldElemPtr s.mem a := coordPtr_zero a ▸ isCoordPtr ha 0
  have pbX : IsFieldElemPtr s.mem b := coordPtr_zero b ▸ isCoordPtr hb 0

  -- the input bounds, in the `readLimb?` form the callees take
  have baZ := limbBounds_readLimb? (isCoordPtr ha 3) (coordLimbBounds ha haLimbs 3)
  have baY := limbBounds_readLimb? (isCoordPtr ha 1) (coordLimbBounds ha haLimbs 1)
  have bbY := limbBounds_readLimb? (isCoordPtr hb 1) (coordLimbBounds hb hbLimbs 1)
  have baX : ∀ (i : Fin 5) (l : ℕ), readLimb? a i s.mem = some l → l ≤ 2 ^ 51 :=
    coordPtr_zero a ▸ limbBounds_readLimb? (isCoordPtr ha 0) (coordLimbBounds ha haLimbs 0)
  have bbX : ∀ (i : Fin 5) (l : ℕ), readLimb? b i s.mem = some l → l ≤ 2 ^ 51 :=
    coordPtr_zero b ▸ limbBounds_readLimb? (isCoordPtr hb 0) (coordLimbBounds hb hbLimbs 0)

  -- `fd_f25519_t x1[1], y1[1]`
  obtain ⟨x1, s₁, hx1def, hs₁def, hs₁, hfitx1, hx1id, hx1off, hctr₁, -⟩ :=
    GlobalState.exists_afterAlloca_facts s hs (5 * 64)
  obtain ⟨y1, s₂, hy1def, hs₂def, hs₂, hfity1, hy1id, hy1off, -, hfry1⟩ :=
    GlobalState.exists_afterAlloca_facts s₁ hs₁ (5 * 64)
  have hxy : y1.id ≠ x1.id := fun h => by rw [h, hx1id, hctr₁] at hy1id; omega

  -- one frame fact through both allocas; everything below `s`'s counter -- the
  -- caller's `a` and `b` included -- rides it to the end of the region
  have fb₁ : FrameBelow s.alloc.nextFreeBlock s s₁ :=
    hs₁def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
  have fb₂ : FrameBelow s.alloc.nextFreeBlock s s₂ :=
    hs₂def ▸ FrameBelow.afterAlloca (by omega) fb₁

  -- the pointer-shaped form the callee obligations take
  have hold : ∀ r : Pointer, IsFieldElemPtr s.mem r → r.id.id < s.alloc.nextFreeBlock :=
    fun r hr => lt_nextFreeBlock_of_fits hs hr.left
  have hS₂ : ∀ r : Pointer, IsFieldElemPtr s.mem r → s₂.mem.live? r.id = s.mem.live? r.id :=
    fun r hr => fb₂ r.id (hold r hr)

  -- the locals themselves sit *in* the frame, so `y1`'s `alloca` has to be
  -- stepped over by hand to see `x1`
  have px1₂ : IsFieldElemPtr s₂.mem x1 :=
    ⟨fits_of_live?_eq (hfry1 x1.id (Ne.symm hxy)) hfitx1, by simp [hx1off]⟩
  have py1₂ : IsFieldElemPtr s₂.mem y1 := ⟨hfity1, by simp [hy1off]⟩

  -- `fd_f25519_mul( x1, b->X, a->Z )`
  obtain ⟨x1bits, hx1val, bx1', x1state, hx1state, hx1state_eq⟩ :=
    fd_f25519_mul_conforms x1 b (a.withOffset 120) s₂ hs₂ px1₂
      (isFieldElemPtr_of_live?_eq (hS₂ b pbX) pbX)
      (isFieldElemPtr_of_live?_eq (hS₂ _ paZ) paZ)
      (limbBounds_of_live?_eq (hS₂ b pbX) (fun i l h => (bbX i l h).trans (by norm_num)))
      (limbBounds_of_live?_eq (hS₂ _ paZ) (fun i l h => (baZ i l h).trans (by norm_num)))

  -- the callee states its result as a readback; the limbs it wrote are what
  -- the comparisons below rewrite with
  have hx1bits : decodeFieldElem (fun i => (x1bits.extractLsb' (64 * i.toNat) 64).toNat)
      = readFieldElem (isFieldElemPtr_of_live?_eq (hS₂ b pbX) pbX)
        * readFieldElem (isFieldElemPtr_of_live?_eq (hS₂ _ paZ) paZ) :=
    (readFieldElem_eq_of (readFieldElem?_splice x1bits px1₂.left)).symm.trans hx1val
  have bx1 : ∀ (i : Fin 5) (l : ℕ),
      readLimb? x1 i (s₂.mem.splice x1 x1bits) = some l → l ≤ 0x8000000000000 :=
    limbBounds_readLimb? _ bx1'

  -- the frame fact speaks only about blocks that predate the region; the
  -- *sibling local* is above the counter, so it needs the write's own equation
  have hlivex1 : ∀ r : BlockId, r ≠ x1.id → x1state.mem.live? r = s₂.mem.live? r :=
    fun r hr => (hx1state_eq.live r).symm.trans (live?_splice_ne (Ne.symm hr))
  have fbX : FrameBelow s.alloc.nextFreeBlock s x1state :=
    FrameBelow.of_equiv hx1state_eq (FrameBelow.splice (by omega) fb₂)
  have hX : ∀ r : Pointer, IsFieldElemPtr s.mem r → x1state.mem.live? r.id = s.mem.live? r.id :=
    fun r hr => fbX r.id (hold r hr)
  have hx1WF : x1state.WF := GlobalState.WF.of_equiv hs₂.splice hx1state_eq
  have px1X : IsFieldElemPtr x1state.mem x1 :=
    isFieldElemPtr_of_live?_eq (hx1state_eq.live x1.id).symm ⟨fits_splice px1₂.left, px1₂.right⟩
  have bx1X : ∀ (i : Fin 5) (l : ℕ), readLimb? x1 i x1state.mem = some l → l ≤ 2 ^ 51 :=
    limbBounds_of_live?_eq (m := (s₂.mem.splice x1 x1bits)) (hx1state_eq.live x1.id).symm
      (fun i l h => (bx1 i l h).trans (by norm_num))
  have py1X : IsFieldElemPtr x1state.mem y1 :=
    isFieldElemPtr_of_live?_eq (hlivex1 y1.id hxy) py1₂

  -- `fd_f25519_mul( y1, b->Y, a->Z )`
  obtain ⟨y1bits, hy1val, by1', y1state, hy1state, hy1state_eq⟩ :=
    fd_f25519_mul_conforms y1 (b.withOffset 40) (a.withOffset 120) x1state hx1WF py1X
      (isFieldElemPtr_of_live?_eq (hX _ pbY) pbY)
      (isFieldElemPtr_of_live?_eq (hX _ paZ) paZ)
      (limbBounds_of_live?_eq (hX _ pbY) (fun i l h => (bbY i l h).trans (by norm_num)))
      (limbBounds_of_live?_eq (hX _ paZ) (fun i l h => (baZ i l h).trans (by norm_num)))

  have hy1bits : decodeFieldElem (fun i => (y1bits.extractLsb' (64 * i.toNat) 64).toNat)
      = readFieldElem (isFieldElemPtr_of_live?_eq (hX _ pbY) pbY)
        * readFieldElem (isFieldElemPtr_of_live?_eq (hX _ paZ) paZ) :=
    (readFieldElem_eq_of (readFieldElem?_splice y1bits py1X.left)).symm.trans hy1val
  have by1 : ∀ (i : Fin 5) (l : ℕ),
      readLimb? y1 i (x1state.mem.splice y1 y1bits) = some l → l ≤ 0x8000000000000 :=
    limbBounds_readLimb? _ by1'

  have hlivey1 : ∀ r : BlockId, r ≠ y1.id → y1state.mem.live? r = x1state.mem.live? r :=
    fun r hr => (hy1state_eq.live r).symm.trans (live?_splice_ne (Ne.symm hr))
  have fbY : FrameBelow s.alloc.nextFreeBlock s y1state :=
    FrameBelow.of_equiv hy1state_eq (FrameBelow.splice (by omega) fbX)
  have hY : ∀ r : Pointer, IsFieldElemPtr s.mem r → y1state.mem.live? r.id = s.mem.live? r.id :=
    fun r hr => fbY r.id (hold r hr)
  have hy1WF : y1state.WF := GlobalState.WF.of_equiv hx1WF.splice hy1state_eq
  have py1Y : IsFieldElemPtr y1state.mem y1 :=
    isFieldElemPtr_of_live?_eq (hy1state_eq.live y1.id).symm ⟨fits_splice py1X.left, py1X.right⟩
  have by1Y : ∀ (i : Fin 5) (l : ℕ), readLimb? y1 i y1state.mem = some l → l ≤ 2 ^ 51 :=
    limbBounds_of_live?_eq (m := (x1state.mem.splice y1 y1bits)) (hy1state_eq.live y1.id).symm
      (fun i l h => (by1 i l h).trans (by norm_num))
  have px1Y : IsFieldElemPtr y1state.mem x1 :=
    isFieldElemPtr_of_live?_eq (hlivey1 x1.id (Ne.symm hxy)) px1X
  have paXY : IsFieldElemPtr y1state.mem a := isFieldElemPtr_of_live?_eq (hY a paX) paX

  -- `fd_f25519_eq( x1, a->X )`
  obtain ⟨eqx1state, heqx1state, heqx1state_eq⟩ :=
    fd_f25519_eq_conforms x1 a y1state hy1WF px1Y paXY
      (limbBounds_of_readLimb? px1Y (limbBounds_of_live?_eq (hlivey1 x1.id (Ne.symm hxy)) bx1X))
      (LimbBounds.bias (limbBounds_of_readLimb? paXY (limbBounds_of_live?_eq (hY a paX) baX)))

  -- the comparison writes nothing at all
  have fbE : FrameBelow s.alloc.nextFreeBlock s eqx1state := FrameBelow.of_equiv heqx1state_eq fbY
  have hE : ∀ r : Pointer, IsFieldElemPtr s.mem r → eqx1state.mem.live? r.id = s.mem.live? r.id :=
    fun r hr => fbE r.id (hold r hr)
  have heqx1WF : eqx1state.WF := GlobalState.WF.of_equiv hy1WF heqx1state_eq
  have py1E : IsFieldElemPtr eqx1state.mem y1 :=
    isFieldElemPtr_of_live?_eq (heqx1state_eq.live y1.id).symm py1Y
  have paYE : IsFieldElemPtr eqx1state.mem (a.withOffset 40) :=
    isFieldElemPtr_of_live?_eq (hE _ paY) paY

  -- `fd_f25519_eq( y1, a->Y )`
  obtain ⟨eqy1state, heqy1state, heqy1state_eq⟩ :=
    fd_f25519_eq_conforms y1 (a.withOffset 40) eqx1state heqx1WF py1E paYE
      (limbBounds_of_readLimb? py1E
        (limbBounds_of_live?_eq (heqx1state_eq.live y1.id).symm by1Y))
      (LimbBounds.bias (limbBounds_of_readLimb? paYE (limbBounds_of_live?_eq (hE _ paY) baY)))

  -- the region's frame holds only `x1` and `y1`, so popping it restores `s`
  have fbF : FrameBelow s.alloc.nextFreeBlock s eqy1state := FrameBelow.of_equiv heqy1state_eq fbE

  refine ⟨s.popFrame eqy1state.mem, ?_,
    GlobalState.Equiv.symm (FrameBelow.popFrame_equiv hs fbF)⟩

  refine run_runFunction (s' := eqy1state) ?_

  denote_step_all v 0
  denote_eval v 0 0
  simp only [LLVM.const?] at hv0
  subst hv0

  peel_alloca from s as s₁ with hs₁def
  peel_alloca from s₁ as s₂ with hs₂def
  -- `peel_alloca` leaves the fresh pointers expanded; the callee equations name
  -- them `x1` and `y1`
  rw [← hx1def, ← hy1def]
  peel_lifetime
  peel_lifetime

  have haFits₂ : Fits s₂.mem a (4 * 5 * 64) :=
    fits_of_live?_eq (fb₂ a.id (lt_nextFreeBlock_of_fits hs ha.1)) ha.1
  peel_gep 120 with a, haFits₂, s₂ as aZ

  peel_call hx1state

  have hbFitsX : Fits x1state.mem b (4 * 5 * 64) := fits_of_live?_eq (hX b pbX) hb.1
  peel_gep 40 with b, hbFitsX, x1state as bY
  peel_call hy1state
  peel_call heqx1state

  have haFitsE : Fits eqx1state.mem a (4 * 5 * 64) := fits_of_live?_eq (hE a paX) ha.1
  peel_gep 40 with a, haFitsE, eqx1state as aY
  peel_call heqy1state

  -- `%10 = and %9, %7`, the two lifetime ends, and the return
  denote_step_all v 10
  eval_llvm 10
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
    rw [readFieldElem?_of_live?_eq (heqx1state_eq.live y1.id).symm,
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

  -- the comparisons are stated over the elements themselves, so read each back
  rw [hv10, readFieldElem_eq_of hx1read, readFieldElem_eq_of hy1read,
    readFieldElem_eq_of haXread, readFieldElem_eq_of haYread]
  by_cases hA : (readPoint hb).Y * (readPoint ha).Z = (readPoint ha).Y <;>
    by_cases hB : (readPoint hb).X * (readPoint ha).Z = (readPoint ha).X
  · rw [if_pos hA, if_pos hB, if_pos (hsame.mpr ⟨hA, hB⟩)]; rfl
  · rw [if_pos hA, if_neg hB, if_neg fun h => hB (hsame.mp h).2]; rfl
  · rw [if_neg hA, if_pos hB, if_neg fun h => hA (hsame.mp h).1]; rfl
  · rw [if_neg hA, if_neg hB, if_neg fun h => hA (hsame.mp h).1]; rfl

end Firedancer.Ref

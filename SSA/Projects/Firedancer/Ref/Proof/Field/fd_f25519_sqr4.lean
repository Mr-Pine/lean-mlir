/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Spec.Field.fd_f25519_sqr4
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_sqr

/-!
# `fd_f25519_sqr4` conformance (ref)

Four `fd_f25519_sqr` calls. A later call's operands sit in blocks no earlier
call wrote (`live?_of_step_ne`); an earlier output survives the later stores
because the destinations are `FieldApart`.
-/

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-! ### Sequential field-element writes

Helpers shared with `fd_f25519_mul3`/`fd_f25519_mul4`: a callee whose result is
`≈` one 320-bit store, transported past later stores that miss it. -/

theorem FieldApart.symm {p q : Pointer} (h : FieldApart p q) : FieldApart q p := by
  rcases h with h | h | h
  · exact .inl (Ne.symm h)
  · exact .inr (.inr h)
  · exact .inr (.inl h)

/-- A limb read passes over a field-element store apart from it. -/
theorem readLimb?_splice_of_fieldApart {m : MemoryState} {p q : Pointer} {x : BitVec (5 * 64)}
    (h : FieldApart q p) (i : Fin 5) : readLimb? p i (m.splice q x) = readLimb? p i m := by
  have hi : i.toNat < 5 := i.isLt
  refine readLimb?_splice_of_disjoint i ?_
  rcases h with h | h | h
  · exact .inl h
  · exact .inr (.inl (by omega))
  · exact .inr (.inr (by omega))

/-- A limb read at `p` just after a store at `p` sees only the stored bits. -/
theorem readLimb?_splice_self_congr {m m' : MemoryState} {p : Pointer} (x : BitVec (5 * 64))
    (hm : Fits m p (5 * 64)) (hm' : Fits m' p (5 * 64)) (i : Fin 5) :
    readLimb? p i (m.splice p x) = readLimb? p i (m'.splice p x) := by
  rw [limbSpliceReadback _ _ _ hm, limbSpliceReadback _ _ _ hm']

/-- Equal limb reads are equal field elements. -/
theorem readFieldElem_eq_of_readLimb?_eq {m m' : MemoryState} {p : Pointer} {h : IsFieldElemPtr m p}
    {h' : IsFieldElemPtr m' p} (hl : ∀ i, readLimb? p i m = readLimb? p i m') :
    readFieldElem h = readFieldElem h' := by simp only [readFieldElem, readFieldElem?, hl]

/-- ... and carry the limb bounds. -/
theorem limbBounds_of_readLimb?_eq {m m' : MemoryState} {p : Pointer} {bound : ℕ}
    {h : IsFieldElemPtr m p} {h' : IsFieldElemPtr m' p}
    (hl : ∀ i, readLimb? p i m = readLimb? p i m') (hb : LimbBounds h' bound) :
    LimbBounds h bound :=
  limbBounds_of_readLimb? h fun j l hj => limbBounds_readLimb? h' hb j l ((hl j).symm.trans hj)

/-- A callee `≈` one store at `d` leaves every other block alone. -/
theorem live?_of_step_ne {w u : GlobalState} {d : Pointer} {n : Nat} {x : BitVec n}
    (he : ({ w with mem := w.mem.splice d x } : GlobalState) ≈ u) {b : BlockId} (hb : d.id ≠ b) :
    u.mem.live? b = w.mem.live? b :=
  (he.live b).symm.trans (live?_splice_ne hb)

/-- ... and keeps every field element in place. -/
theorem isFieldElemPtr_of_step {w u : GlobalState} {d q : Pointer} {n : Nat} {x : BitVec n}
    (he : ({ w with mem := w.mem.splice d x } : GlobalState) ≈ u) (hq : IsFieldElemPtr w.mem q) :
    IsFieldElemPtr u.mem q :=
  isFieldElemPtr_of_live?_eq (he.live q.id).symm (isFieldElemPtr_splice hq)

theorem fd_f25519_sqr4_conforms (r1 a1 r2 a2 r3 a3 r4 a4 : Pointer) (s : GlobalState) (hs : s.WF)
    (hdst : [r1, r2, r3, r4].Pairwise FieldApart)
    (hsrc : ∀ d ∈ [r1, r2, r3, r4], ∀ x ∈ [a1, a2, a3, a4], d.id ≠ x.id)
    (hr1 : IsFieldElemPtr s.mem r1) (ha1 : IsFieldElemPtr s.mem a1) (hr2 : IsFieldElemPtr s.mem r2)
    (ha2 : IsFieldElemPtr s.mem a2) (hr3 : IsFieldElemPtr s.mem r3) (ha3 : IsFieldElemPtr s.mem a3)
    (hr4 : IsFieldElemPtr s.mem r4) (ha4 : IsFieldElemPtr s.mem a4)
    (hbounds :
      ∀ x ∈ [a1, a2, a3, a4],
        ∀ (i : Fin 5) (l : ℕ), readLimb? x i s.mem = some l → l ≤ 0x18000000000000) :
    fd_f25519_sqr4_spec r1 a1 r2 a2 r3 a3 r4 a4 s hdst hsrc hr1 ha1 hr2 ha2 hr3 ha3 hr4 ha4 := by
  simp only [fd_f25519_sqr4_spec, Cfg.denote]
  have d12 : FieldApart r1 r2 := List.rel_of_pairwise_cons hdst (by simp)
  have d13 : FieldApart r1 r3 := List.rel_of_pairwise_cons hdst (by simp)
  have d14 : FieldApart r1 r4 := List.rel_of_pairwise_cons hdst (by simp)
  have d23 : FieldApart r2 r3 := List.rel_of_pairwise_cons hdst.of_cons (by simp)
  have d24 : FieldApart r2 r4 := List.rel_of_pairwise_cons hdst.of_cons (by simp)
  have d34 : FieldApart r3 r4 := List.rel_of_pairwise_cons hdst.of_cons.of_cons (by simp)
  have s12 : r1.id ≠ a2.id := hsrc r1 (by simp) a2 (by simp)
  have s13 : r1.id ≠ a3.id := hsrc r1 (by simp) a3 (by simp)
  have s23 : r2.id ≠ a3.id := hsrc r2 (by simp) a3 (by simp)
  have s14 : r1.id ≠ a4.id := hsrc r1 (by simp) a4 (by simp)
  have s24 : r2.id ≠ a4.id := hsrc r2 (by simp) a4 (by simp)
  have s34 : r3.id ≠ a4.id := hsrc r3 (by simp) a4 (by simp)
  -- call 1, in `s`
  obtain ⟨o1, hv1, hb1, ⟨u₁, hrun₁, heq₁⟩⟩ :=
    fd_f25519_sqr_conforms r1 a1 s hs hr1 ha1 (hbounds a1 (by simp))
  have hu₁ : u₁.WF := GlobalState.WF.of_equiv hs.splice heq₁
  -- call 2, in `u₁`
  have hr2u : IsFieldElemPtr u₁.mem r2 := isFieldElemPtr_of_step heq₁ hr2
  have ha2l : u₁.mem.live? a2.id = s.mem.live? a2.id := live?_of_step_ne heq₁ s12
  have ha2u : IsFieldElemPtr u₁.mem a2 := isFieldElemPtr_of_live?_eq ha2l ha2
  obtain ⟨o2, hv2, hb2, ⟨u₂, hrun₂, heq₂⟩⟩ :=
    fd_f25519_sqr_conforms r2 a2 u₁ hu₁ hr2u ha2u
      (limbBounds_of_live?_eq ha2l (hbounds a2 (by simp)))
  have hu₂ : u₂.WF := GlobalState.WF.of_equiv hu₁.splice heq₂
  -- call 3, in `u₂`
  have hr3u : IsFieldElemPtr u₂.mem r3 :=
    isFieldElemPtr_of_step heq₂ (isFieldElemPtr_of_step heq₁ hr3)
  have ha3l : u₂.mem.live? a3.id = s.mem.live? a3.id :=
    (live?_of_step_ne heq₂ s23).trans (live?_of_step_ne heq₁ s13)
  have ha3u : IsFieldElemPtr u₂.mem a3 := isFieldElemPtr_of_live?_eq ha3l ha3
  obtain ⟨o3, hv3, hb3, ⟨u₃, hrun₃, heq₃⟩⟩ :=
    fd_f25519_sqr_conforms r3 a3 u₂ hu₂ hr3u ha3u
      (limbBounds_of_live?_eq ha3l (hbounds a3 (by simp)))
  have hu₃ : u₃.WF := GlobalState.WF.of_equiv hu₂.splice heq₃
  -- call 4, in `u₃`
  have hr4u : IsFieldElemPtr u₃.mem r4 :=
    isFieldElemPtr_of_step heq₃ (isFieldElemPtr_of_step heq₂ (isFieldElemPtr_of_step heq₁ hr4))
  have ha4l : u₃.mem.live? a4.id = s.mem.live? a4.id :=
    (live?_of_step_ne heq₃ s34).trans
      ((live?_of_step_ne heq₂ s24).trans (live?_of_step_ne heq₁ s14))
  have ha4u : IsFieldElemPtr u₃.mem a4 := isFieldElemPtr_of_live?_eq ha4l ha4
  obtain ⟨o4, hv4, hb4, ⟨u₄, hrun₄, heq₄⟩⟩ :=
    fd_f25519_sqr_conforms r4 a4 u₃ hu₃ hr4u ha4u
      (limbBounds_of_live?_eq ha4l (hbounds a4 (by simp)))
  have hu₄ : u₄.WF := GlobalState.WF.of_equiv hu₃.splice heq₄
  refine ⟨packLimbs o1, packLimbs o2, packLimbs o3, packLimbs o4, ?_⟩
  -- each output limb, read in the final memory, is the one its callee wrote
  have l1 :
    ∀ i,
      readLimb? r1 i
          ((((s.mem.splice r1 (packLimbs o1)).splice r2 (packLimbs o2)).splice r3
                (packLimbs o3)).splice
            r4 (packLimbs o4)) =
        readLimb? r1 i (s.mem.splice r1 (packLimbs o1)) :=
    fun i =>
    (readLimb?_splice_of_fieldApart d14.symm i).trans
      ((readLimb?_splice_of_fieldApart d13.symm i).trans
        (readLimb?_splice_of_fieldApart d12.symm i))
  have l2 :
    ∀ i,
      readLimb? r2 i
          ((((s.mem.splice r1 (packLimbs o1)).splice r2 (packLimbs o2)).splice r3
                (packLimbs o3)).splice
            r4 (packLimbs o4)) =
        readLimb? r2 i (u₁.mem.splice r2 (packLimbs o2)) :=
    fun i =>
    (readLimb?_splice_of_fieldApart d24.symm i).trans
      ((readLimb?_splice_of_fieldApart d23.symm i).trans
        (readLimb?_splice_self_congr _ (fits_splice hr2.1) hr2u.1 i))
  have l3 :
    ∀ i,
      readLimb? r3 i
          ((((s.mem.splice r1 (packLimbs o1)).splice r2 (packLimbs o2)).splice r3
                (packLimbs o3)).splice
            r4 (packLimbs o4)) =
        readLimb? r3 i (u₂.mem.splice r3 (packLimbs o3)) :=
    fun i =>
    (readLimb?_splice_of_fieldApart d34.symm i).trans
      (readLimb?_splice_self_congr _ (fits_splice (fits_splice hr3.1)) hr3u.1 i)
  have l4 :
    ∀ i,
      readLimb? r4 i
          ((((s.mem.splice r1 (packLimbs o1)).splice r2 (packLimbs o2)).splice r3
                (packLimbs o3)).splice
            r4 (packLimbs o4)) =
        readLimb? r4 i (u₃.mem.splice r4 (packLimbs o4)) :=
    fun i => readLimb?_splice_self_congr _ (fits_splice (fits_splice (fits_splice hr4.1))) hr4u.1 i
  refine
    ⟨⟨s.popFrame u₄.mem, run_runFunction (s' := u₄) ?run, ?equiv⟩,
      (readFieldElem_eq_of_readLimb?_eq l1).trans hv1, limbBounds_of_readLimb?_eq l1 hb1,
      (readFieldElem_eq_of_readLimb?_eq l2).trans
        (hv2.trans
          (by rw [readFieldElem_eq_of_readLimb?_eq (readLimb?_of_live?_eq ha2l) (h' := ha2)])),
      limbBounds_of_readLimb?_eq l2 hb2,
      (readFieldElem_eq_of_readLimb?_eq l3).trans
        (hv3.trans
          (by rw [readFieldElem_eq_of_readLimb?_eq (readLimb?_of_live?_eq ha3l) (h' := ha3)])),
      limbBounds_of_readLimb?_eq l3 hb3,
      (readFieldElem_eq_of_readLimb?_eq l4).trans
        (hv4.trans
          (by rw [readFieldElem_eq_of_readLimb?_eq (readLimb?_of_live?_eq ha4l) (h' := ha4)])),
      limbBounds_of_readLimb?_eq l4 hb4⟩
  case
    equiv =>
    have c₂ := GlobalState.Equiv.trans (splice_equiv (p := r2) (x := packLimbs o2) heq₁) heq₂
    have c₃ := GlobalState.Equiv.trans (splice_equiv (p := r3) (x := packLimbs o3) c₂) heq₃
    have c₄ := GlobalState.Equiv.trans (splice_equiv (p := r4) (x := packLimbs o4) c₃) heq₄
    have halloc : u₄.alloc = s.alloc := c₄.1.symm
    have hpop : (s.popFrame u₄.mem : GlobalState) ≈ u₄ :=
      GlobalState.Equiv.trans
        (killFrom_equiv_of_none
          (fun b hb =>
            hu₄ b
              (by
                rw [halloc]; omega)))
        ⟨halloc.symm, c₄.globals, fun _ => rfl⟩
    exact GlobalState.Equiv.trans c₄ (GlobalState.Equiv.symm hpop)
  case
    run =>
    refine (BlockCom.run_bind_denote_call_of_value (x := PoisonOr.value r1) (s' := u₁) ?_).trans ?_
    · exact hrun₁
    refine (BlockCom.run_bind_denote_call_of_value (x := PoisonOr.value r2) (s' := u₂) ?_).trans ?_
    · exact hrun₂
    refine (BlockCom.run_bind_denote_call_of_value (x := PoisonOr.value r3) (s' := u₃) ?_).trans ?_
    · exact hrun₃
    refine (BlockCom.run_bind_denote_call_of_value (x := PoisonOr.value r4) (s' := u₄) ?_).trans ?_
    · exact hrun₄
    rfl

end Firedancer.Ref

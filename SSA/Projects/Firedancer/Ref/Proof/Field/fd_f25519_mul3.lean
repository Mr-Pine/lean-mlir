/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Spec.Field.fd_f25519_mul3
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_mul
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_sqr4

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

theorem fd_f25519_mul3_conforms (r1 a1 b1 r2 a2 b2 r3 a3 b3 : Pointer) (s : GlobalState) (hs : s.WF)
    (hdst : [r1, r2, r3].Pairwise FieldApart)
    (hsrc : ∀ d ∈ [r1, r2, r3], ∀ x ∈ [a1, b1, a2, b2, a3, b3], d.id ≠ x.id)
    (hr1 : IsFieldElemPtr s.mem r1) (ha1 : IsFieldElemPtr s.mem a1) (hb1 : IsFieldElemPtr s.mem b1)
    (hr2 : IsFieldElemPtr s.mem r2) (ha2 : IsFieldElemPtr s.mem a2) (hb2 : IsFieldElemPtr s.mem b2)
    (hr3 : IsFieldElemPtr s.mem r3) (ha3 : IsFieldElemPtr s.mem a3) (hb3 : IsFieldElemPtr s.mem b3)
    (hbounds : ∀ x ∈ [a1, b1, a2, b2, a3, b3],
      ∀ (i : Fin 5) (l : ℕ), readLimb? x i s.mem = some l → l ≤ 0x18000000000000) :
    fd_f25519_mul3_spec r1 a1 b1 r2 a2 b2 r3 a3 b3 s hdst hsrc hr1 ha1 hb1 hr2 ha2 hb2 hr3 ha3 hb3 := by
  simp only [fd_f25519_mul3_spec, Cfg.denote]
  have d12 : FieldApart r1 r2 := List.rel_of_pairwise_cons hdst (by simp)
  have d13 : FieldApart r1 r3 := List.rel_of_pairwise_cons hdst (by simp)
  have d23 : FieldApart r2 r3 := List.rel_of_pairwise_cons hdst.of_cons (by simp)
  have s1a2 : r1.id ≠ a2.id := hsrc r1 (by simp) a2 (by simp)
  have s1b2 : r1.id ≠ b2.id := hsrc r1 (by simp) b2 (by simp)
  have s1a3 : r1.id ≠ a3.id := hsrc r1 (by simp) a3 (by simp)
  have s1b3 : r1.id ≠ b3.id := hsrc r1 (by simp) b3 (by simp)
  have s2a3 : r2.id ≠ a3.id := hsrc r2 (by simp) a3 (by simp)
  have s2b3 : r2.id ≠ b3.id := hsrc r2 (by simp) b3 (by simp)

  -- call 1, in `s`
  obtain ⟨o1, hv1, hB1, ⟨u₁, hrun₁, heq₁⟩⟩ :=
    fd_f25519_mul_conforms r1 a1 b1 s hs hr1 ha1 hb1 (hbounds a1 (by simp)) (hbounds b1 (by simp))
  have hu₁ : u₁.WF := GlobalState.WF.of_equiv hs.splice heq₁

  -- call 2, in `u₁`
  have hr2u : IsFieldElemPtr u₁.mem r2 := (isFieldElemPtr_of_step heq₁ hr2)
  have ha2l : u₁.mem.live? a2.id = s.mem.live? a2.id := (live?_of_step_ne heq₁ s1a2)
  have ha2u : IsFieldElemPtr u₁.mem a2 := isFieldElemPtr_of_live?_eq ha2l ha2
  have hb2l : u₁.mem.live? b2.id = s.mem.live? b2.id := (live?_of_step_ne heq₁ s1b2)
  have hb2u : IsFieldElemPtr u₁.mem b2 := isFieldElemPtr_of_live?_eq hb2l hb2
  obtain ⟨o2, hv2, hB2, ⟨u₂, hrun₂, heq₂⟩⟩ :=
    fd_f25519_mul_conforms r2 a2 b2 u₁ hu₁ hr2u ha2u hb2u
      (limbBounds_of_live?_eq ha2l (hbounds a2 (by simp)))
      (limbBounds_of_live?_eq hb2l (hbounds b2 (by simp)))
  have hu₂ : u₂.WF := GlobalState.WF.of_equiv hu₁.splice heq₂

  -- call 3, in `u₂`
  have hr3u : IsFieldElemPtr u₂.mem r3 := (isFieldElemPtr_of_step heq₂ (isFieldElemPtr_of_step heq₁ hr3))
  have ha3l : u₂.mem.live? a3.id = s.mem.live? a3.id := ((live?_of_step_ne heq₂ s2a3).trans (live?_of_step_ne heq₁ s1a3))
  have ha3u : IsFieldElemPtr u₂.mem a3 := isFieldElemPtr_of_live?_eq ha3l ha3
  have hb3l : u₂.mem.live? b3.id = s.mem.live? b3.id := ((live?_of_step_ne heq₂ s2b3).trans (live?_of_step_ne heq₁ s1b3))
  have hb3u : IsFieldElemPtr u₂.mem b3 := isFieldElemPtr_of_live?_eq hb3l hb3
  obtain ⟨o3, hv3, hB3, ⟨u₃, hrun₃, heq₃⟩⟩ :=
    fd_f25519_mul_conforms r3 a3 b3 u₂ hu₂ hr3u ha3u hb3u
      (limbBounds_of_live?_eq ha3l (hbounds a3 (by simp)))
      (limbBounds_of_live?_eq hb3l (hbounds b3 (by simp)))
  have hu₃ : u₃.WF := GlobalState.WF.of_equiv hu₂.splice heq₃

  refine ⟨o1, o2, o3, ?_⟩

  -- each output limb, read in the final memory, is the one its callee wrote
  obtain ⟨outMem, houtMem⟩ : ∃ m : MemoryState, m = (((s.mem.splice r1 o1).splice r2 o2).splice r3 o3) := ⟨_, rfl⟩
  have l1 : ∀ i, readLimb? r1 i outMem = readLimb? r1 i (s.mem.splice r1 o1) := by
    intro i; rw [houtMem]
    rw [readLimb?_splice_of_fieldApart d13.symm i, readLimb?_splice_of_fieldApart d12.symm i]
  have l2 : ∀ i, readLimb? r2 i outMem = readLimb? r2 i (u₁.mem.splice r2 o2) := by
    intro i; rw [houtMem]
    rw [readLimb?_splice_of_fieldApart d23.symm i]
    exact readLimb?_splice_self_congr _ (fits_splice hr2.1) hr2u.1 i
  have l3 : ∀ i, readLimb? r3 i outMem = readLimb? r3 i (u₂.mem.splice r3 o3) := by
    intro i; rw [houtMem]
    exact readLimb?_splice_self_congr _ (fits_splice (fits_splice hr3.1)) hr3u.1 i
  subst houtMem
  refine ⟨⟨s.popFrame u₃.mem, run_runFunction (s' := u₃) ?run, ?equiv⟩,
    (readFieldElem_eq_of_readLimb?_eq l1).trans hv1,
    limbBounds_of_readLimb?_eq l1 hB1,
    (readFieldElem_eq_of_readLimb?_eq l2).trans (hv2.trans (by
      rw [readFieldElem_eq_of_readLimb?_eq (readLimb?_of_live?_eq ha2l) (h' := ha2),
        readFieldElem_eq_of_readLimb?_eq (readLimb?_of_live?_eq hb2l) (h' := hb2)])),
    limbBounds_of_readLimb?_eq l2 hB2,
    (readFieldElem_eq_of_readLimb?_eq l3).trans (hv3.trans (by
      rw [readFieldElem_eq_of_readLimb?_eq (readLimb?_of_live?_eq ha3l) (h' := ha3),
        readFieldElem_eq_of_readLimb?_eq (readLimb?_of_live?_eq hb3l) (h' := hb3)])),
    limbBounds_of_readLimb?_eq l3 hB3⟩

  case equiv =>
    have c₂ := GlobalState.Equiv.trans (splice_equiv (p := r2) (x := o2) heq₁) heq₂
    have c₃ := GlobalState.Equiv.trans (splice_equiv (p := r3) (x := o3) c₂) heq₃
    have halloc : u₃.alloc = s.alloc := c₃.1.symm
    have hpop : (s.popFrame u₃.mem : GlobalState) ≈ u₃ :=
      GlobalState.Equiv.trans
        (killFrom_equiv_of_none (fun b hb => hu₃ b (by rw [halloc]; omega)))
        ⟨halloc.symm, c₃.globals, fun _ => rfl⟩
    exact GlobalState.Equiv.trans c₃ (GlobalState.Equiv.symm hpop)

  case run =>
    refine (BlockCom.run_bind_denote_call_of_value (x := PoisonOr.value r1) (s' := u₁) ?_).trans ?_
    · exact hrun₁
    refine (BlockCom.run_bind_denote_call_of_value (x := PoisonOr.value r2) (s' := u₂) ?_).trans ?_
    · exact hrun₂
    refine (BlockCom.run_bind_denote_call_of_value (x := PoisonOr.value r3) (s' := u₃) ?_).trans ?_
    · exact hrun₃
    rfl

end Firedancer.Ref

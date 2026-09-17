/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Ref.Spec.Point.fd_ed25519_point_add_final_mul_projective
public import SSA.Projects.Firedancer.MLIR.DenoteStep
public import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
public import SSA.Projects.Firedancer.Ref.Proof.Point
public import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_mul3

@[expose] public section

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- `wf_splice4` for three stores. -/
theorem wf_splice3 {t : GlobalState} {p₁ p₂ p₃ : Pointer} {w₁ w₂ w₃ : Nat} {x₁ : BitVec w₁}
    {x₂ : BitVec w₂} {x₃ : BitVec w₃} (ht : t.WF) :
    ({ t with mem := ((t.mem.splice p₁ x₁).splice p₂ x₂).splice p₃ x₃ } : GlobalState).WF :=
  fun q hq => live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none (ht q hq)))

theorem fd_ed25519_point_add_final_mul_projective_conforms (r a : Pointer) (s : GlobalState)
    (hs : s.WF) (hne : r.id ≠ a.id) (hr : IsPointPtr s.mem r) (ha : IsPointPtr s.mem a)
    (haX : ∀ (i : Fin 5) (l : ℕ), readLimb? a i s.mem = some l → l ≤ 0x18000000000000)
    (haY :
      ∀ (i : Fin 5) (l : ℕ), readLimb? (a.withOffset 40) i s.mem = some l → l ≤ 0x18000000000000)
    (haZ :
      ∀ (i : Fin 5) (l : ℕ), readLimb? (a.withOffset 120) i s.mem = some l → l ≤ 0x18000000000000)
    (haT :
      ∀ (i : Fin 5) (l : ℕ), readLimb? (a.withOffset 80) i s.mem = some l → l ≤ 0x18000000000000) :
    fd_ed25519_point_add_final_mul_projective_spec r a s hne hr ha := by
  simp only [fd_ed25519_point_add_final_mul_projective_spec, Cfg.denote]
  have hr0 : IsFieldElemPtr s.mem r := by simpa [Pointer.withOffset] using isCoordPtr hr 0
  have hr1 : IsFieldElemPtr s.mem (r.withOffset 40) := coordPtr_one r ▸ isCoordPtr hr 1
  have hr2 : IsFieldElemPtr s.mem (r.withOffset 80) := coordPtr_two r ▸ isCoordPtr hr 2
  have hr3 : IsFieldElemPtr s.mem (r.withOffset 120) := coordPtr_three r ▸ isCoordPtr hr 3
  have ha0 : IsFieldElemPtr s.mem a := by simpa [Pointer.withOffset] using isCoordPtr ha 0
  have ha1 : IsFieldElemPtr s.mem (a.withOffset 40) := coordPtr_one a ▸ isCoordPtr ha 1
  have ha2 : IsFieldElemPtr s.mem (a.withOffset 80) := coordPtr_two a ▸ isCoordPtr ha 2
  have ha3 : IsFieldElemPtr s.mem (a.withOffset 120) := coordPtr_three a ▸ isCoordPtr ha 3
  have h40 : (r.withOffset 40).offsetInBits = r.offsetInBits + 320 := by
    simpa using
      withOffset_offsetInBits (off := 40)
        (by
          have := hr.2; simp; omega)
  have h80 : (r.withOffset 80).offsetInBits = r.offsetInBits + 640 := by
    simpa using
      withOffset_offsetInBits (off := 80)
        (by
          have := hr.2; simp; omega)
  have h120 : (r.withOffset 120).offsetInBits = r.offsetInBits + 960 := by
    simpa using
      withOffset_offsetInBits (off := 120)
        (by
          have := hr.2; simp; omega)
  have hdst : [r, r.withOffset 40, r.withOffset 120].Pairwise FieldApart := by
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true, FieldApart, h40, h120]
    and_intros <;>
      first
      | exact .inr (.inl (by omega))
      | exact fun _ h => h.elim
  have hsrc :
    ∀ d ∈ [r, r.withOffset 40, r.withOffset 120],
      ∀
        x ∈
          [a, a.withOffset 40, a.withOffset 120, a.withOffset 80, a.withOffset 40,
            a.withOffset 120],
        d.id ≠ x.id := by
    intro d hd x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd hx
    rcases hd with rfl | rfl | rfl <;> rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hne
  have hbounds :
    ∀
      x ∈
        [a, a.withOffset 40, a.withOffset 120, a.withOffset 80, a.withOffset 40, a.withOffset 120],
      ∀ (i : Fin 5) (l : ℕ), readLimb? x i s.mem = some l → l ≤ 0x18000000000000 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  obtain ⟨oX, oY, oZ, ⟨st, hrun, heq⟩, hvX, hbX, hvY, hbY, hvZ, hbZ⟩ :=
    fd_f25519_mul3_conforms r a (a.withOffset 40) (r.withOffset 40) (a.withOffset 120)
      (a.withOffset 80) (r.withOffset 120) (a.withOffset 40) (a.withOffset 120) s hs hdst hsrc hr0
      ha0 ha1 hr1 ha3 ha2 hr3 ha1 ha3 hbounds
  have hstWF : st.WF := (wf_splice3 hs).of_equiv heq
  refine
    ⟨oX, oY, oZ, ⟨s.popFrame st.mem, run_runFunction (s' := st) ?run, ?equiv⟩, ?val,
      limbBounds_congr (by simp [Pointer.withOffset]) hbX,
      limbBounds_congr (coordPtr_one r).symm hbY, limbBounds_congr (coordPtr_three r).symm hbZ⟩
  case
    equiv =>
    have hpop : (s.popFrame st.mem : GlobalState) ≈ st :=
      GlobalState.Equiv.trans
        (killFrom_equiv_of_none
          (fun b hb =>
            hstWF b
              (by
                rw [← heq.1]; omega)))
        ⟨heq.1, heq.globals, fun _ => rfl⟩
    exact GlobalState.Equiv.trans heq (GlobalState.Equiv.symm hpop)
  case val =>
    -- `T` sits apart from all three stores
    have d0 : FieldApart r (r.withOffset 80) := .inr (.inl (by omega))
    have d1 : FieldApart (r.withOffset 40) (r.withOffset 80) := .inr (.inl (by omega))
    have d3 : FieldApart (r.withOffset 120) (r.withOffset 80) := .inr (.inr (by omega))
    have hT :
      readFieldElem
          (isFieldElemPtr_splice
            (isFieldElemPtr_splice (isFieldElemPtr_splice (p := r) (x := oX) hr2) (p :=
              r.withOffset 40) (x := oY))
            (p := r.withOffset 120) (x := oZ)) =
        readFieldElem hr2 :=
      readFieldElem_eq_of_readLimb?_eq fun i => by
        rw [readLimb?_splice_of_fieldApart d3, readLimb?_splice_of_fieldApart d1,
          readLimb?_splice_of_fieldApart d0]
    rw [readPoint_eq_of _ hvX hvY hT hvZ,
      readPoint_eq_of ha (h0 := ha0) (h1 := ha1) (h2 := ha2) (h3 := ha3) rfl rfl rfl rfl,
      readPoint_eq_of hr (h0 := hr0) (h1 := hr1) (h2 := hr2) (h3 := hr3) rfl rfl rfl rfl]
    rfl
  case run =>
    denote_step_reduce v 4 [gepConst, ptradd, LLVM.const?]
    have e0 : v0 = .value (a.withOffset 40) := by simp [hv0, Pointer.withOffset, simp_sllvm]
    have e1 : v1 = .value (r.withOffset 40) := by simp [hv1, Pointer.withOffset, simp_sllvm]
    have e2 : v2 = .value (a.withOffset 120) := by simp [hv2, Pointer.withOffset, simp_sllvm]
    have e3 : v3 = .value (a.withOffset 80) := by simp [hv3, Pointer.withOffset, simp_sllvm]
    have e4 : v4 = .value (r.withOffset 120) := by simp [hv4, Pointer.withOffset, simp_sllvm]
    subst e0 e1 e2 e3 e4
    clear hv0 hv1 hv2 hv3 hv4
    refine (BlockCom.run_bind_denote_call_of_nil (s' := st) ?_).trans ?_
    · exact hrun
    rfl

end Firedancer.Ref

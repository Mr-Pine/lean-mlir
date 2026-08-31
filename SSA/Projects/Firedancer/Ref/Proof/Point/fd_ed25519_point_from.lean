import SSA.Projects.Firedancer.Ref.Spec.Point.fd_ed25519_point_from
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_from
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Point

import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_set

/-!
# `fd_ed25519_point_from` conformance

Four `fd_f25519_set` calls, one per coordinate, in call order `X, Y, Z, T`
(byte offsets `0, 40, 120, 80`). Each call's conformance hands back an
equivalent-to-a-splice state; the work here is transporting the limb copies
through the later splices -- `readLimb?_splice_of_disjoint`, since all four
land in `r`'s block at disjoint ranges -- and chaining the equivalences.
The equivalence chain leaves its intermediate types inferred: stating them as
record literals makes each `have` re-check the splice chains definitionally,
which is minutes, not seconds.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

set_option maxHeartbeats 800000 in
theorem fd_ed25519_point_from_conforms (r x y z t : Pointer) (s : GlobalState)
    (hs : s.WF)
    (hxne : x.id ≠ r.id) (hyne : y.id ≠ r.id) (hzne : z.id ≠ r.id) (htne : t.id ≠ r.id)
    (hr : IsPointPtr s.mem r)
    (hx : IsFieldElemPtr s.mem x) (hy : IsFieldElemPtr s.mem y)
    (hz : IsFieldElemPtr s.mem z) (ht : IsFieldElemPtr s.mem t) :
    fd_ed25519_point_from_spec r x y z t s hxne hyne hzne htne := by
  simp only [fd_ed25519_point_from_spec, Cfg.denote]

  -- the four coordinate pointers, as field elements in `s`
  have hc0 : IsFieldElemPtr s.mem r := by
    simpa [Pointer.withOffset] using isCoordPtr r hr 0
  have hc1 : IsFieldElemPtr s.mem (r.withOffset 40) := coordPtr_one r ▸ isCoordPtr r hr 1
  have hc3 : IsFieldElemPtr s.mem (r.withOffset 120) := coordPtr_three r ▸ isCoordPtr r hr 3
  have hc2 : IsFieldElemPtr s.mem (r.withOffset 80) := by
    simpa [Pointer.withOffset] using isCoordPtr r hr 2

  -- call 1: X ≔ x, in `s`
  obtain ⟨oX, ⟨u₁, hrun₁, heq₁⟩, hcopy₁⟩ :=
    fd_f25519_set_conforms r x s hs (Ne.symm hxne) hc0 hx
  have hu₁WF : u₁.WF := GlobalState.WF.of_equiv hs.splice heq₁

  -- call 2: Y ≔ y, in `u₁`
  have hc1u : IsFieldElemPtr u₁.mem (r.withOffset 40) :=
    ⟨fits_equiv heq₁ (by simpa using fits_splice hc1.1), hc1.2⟩
  have hyu : IsFieldElemPtr u₁.mem y :=
    ⟨fits_equiv heq₁ (by simpa using fits_splice hy.1), hy.2⟩
  obtain ⟨oY, ⟨u₂, hrun₂, heq₂⟩, hcopy₂⟩ :=
    fd_f25519_set_conforms (r.withOffset 40) y u₁ hu₁WF (Ne.symm hyne) hc1u hyu
  have hu₂WF : u₂.WF := GlobalState.WF.of_equiv hu₁WF.splice heq₂

  -- call 3: Z ≔ z, in `u₂`
  have hc3u : IsFieldElemPtr u₂.mem (r.withOffset 120) :=
    ⟨fits_equiv heq₂ (by simpa using fits_splice (fits_equiv heq₁
      (by simpa using fits_splice hc3.1))), hc3.2⟩
  have hzu : IsFieldElemPtr u₂.mem z :=
    ⟨fits_equiv heq₂ (by simpa using fits_splice (fits_equiv heq₁
      (by simpa using fits_splice hz.1))), hz.2⟩
  obtain ⟨oZ, ⟨u₃, hrun₃, heq₃⟩, hcopy₃⟩ :=
    fd_f25519_set_conforms (r.withOffset 120) z u₂ hu₂WF (Ne.symm hzne) hc3u hzu
  have hu₃WF : u₃.WF := GlobalState.WF.of_equiv hu₂WF.splice heq₃

  -- call 4: T ≔ t, in `u₃`
  have hc2u : IsFieldElemPtr u₃.mem (r.withOffset 80) :=
    ⟨fits_equiv heq₃ (by simpa using fits_splice (fits_equiv heq₂
      (by simpa using fits_splice (fits_equiv heq₁
        (by simpa using fits_splice hc2.1))))), hc2.2⟩
  have htu : IsFieldElemPtr u₃.mem t :=
    ⟨fits_equiv heq₃ (by simpa using fits_splice (fits_equiv heq₂
      (by simpa using fits_splice (fits_equiv heq₁
        (by simpa using fits_splice ht.1))))), ht.2⟩
  obtain ⟨oT, ⟨u₄, hrun₄, heq₄⟩, hcopy₄⟩ :=
    fd_f25519_set_conforms (r.withOffset 80) t u₃ hu₃WF (Ne.symm htne) hc2u htu
  have hu₄WF : u₄.WF := GlobalState.WF.of_equiv hu₃WF.splice heq₄

  refine ⟨oX, oY, oZ, oT, ?_⟩

  -- coordinate offsets in bits; `hr.right` rules out wrapping
  have h40 : (r.withOffset 40).offsetInBits = r.offsetInBits + 320 := by
    simpa using withOffset_offsetInBits (off := 40) (by have := hr.2; simp; omega)
  have h80 : (r.withOffset 80).offsetInBits = r.offsetInBits + 640 := by
    simpa using withOffset_offsetInBits (off := 80) (by have := hr.2; simp; omega)
  have h120 : (r.withOffset 120).offsetInBits = r.offsetInBits + 960 := by
    simpa using withOffset_offsetInBits (off := 120) (by have := hr.2; simp; omega)

  refine ⟨⟨s.popFrame u₄.mem, run_runFunction (s' := u₄) ?run, ?equiv⟩, ?vx, ?vy, ?vt, ?vz⟩

  case vx =>
    intro i
    have hi : i.toNat < 5 := i.isLt
    rw [readLimb?_splice_of_disjoint i (.inr (.inr (by rw [h80]; omega))),
      readLimb?_splice_of_disjoint i (.inr (.inr (by rw [h120]; omega))),
      readLimb?_splice_of_disjoint i (.inr (.inr (by rw [h40]; omega)))]
    exact hcopy₁ i

  case vy =>
    intro i
    have hi : i.toNat < 5 := i.isLt
    rw [readLimb?_splice_of_disjoint i (.inr (.inr (by rw [h40, h80]; omega))),
      readLimb?_splice_of_disjoint i (.inr (.inr (by rw [h40, h120]; omega))),
      limbSpliceReadback _ _ _ (fits_splice hc1.1) i]
    have h2 := hcopy₂ i
    rw [limbSpliceReadback _ _ _ hc1u.1 i] at h2
    rw [h2, ← readLimb?_of_equiv heq₁ y i]
    exact readLimb?_splice_of_disjoint i (.inl (Ne.symm hyne))

  case vz =>
    intro i
    have hi : i.toNat < 5 := i.isLt
    rw [readLimb?_splice_of_disjoint i (.inr (.inl (by rw [h80, h120]; omega))),
      limbSpliceReadback _ _ _ (fits_splice (fits_splice hc3.1)) i]
    have h3 := hcopy₃ i
    rw [limbSpliceReadback _ _ _ hc3u.1 i] at h3
    have e2 := readLimb?_of_equiv heq₂ z i
    dsimp only at e2
    rw [readLimb?_splice_of_disjoint i
      (.inl (show (r.withOffset 40).id ≠ z.id from Ne.symm hzne))] at e2
    have e1 := readLimb?_of_equiv heq₁ z i
    dsimp only at e1
    rw [readLimb?_splice_of_disjoint i (.inl (Ne.symm hzne))] at e1
    rw [h3, ← e2, ← e1]

  case vt =>
    intro i
    rw [limbSpliceReadback _ _ _ (fits_splice (fits_splice (fits_splice hc2.1))) i]
    have h4 := hcopy₄ i
    rw [limbSpliceReadback _ _ _ hc2u.1 i] at h4
    have e3 := readLimb?_of_equiv heq₃ t i
    dsimp only at e3
    rw [readLimb?_splice_of_disjoint i
      (.inl (show (r.withOffset 120).id ≠ t.id from Ne.symm htne))] at e3
    have e2 := readLimb?_of_equiv heq₂ t i
    dsimp only at e2
    rw [readLimb?_splice_of_disjoint i
      (.inl (show (r.withOffset 40).id ≠ t.id from Ne.symm htne))] at e2
    have e1 := readLimb?_of_equiv heq₁ t i
    dsimp only at e1
    rw [readLimb?_splice_of_disjoint i (.inl (Ne.symm htne))] at e1
    rw [h4, ← e3, ← e2, ← e1]

  case equiv =>
    have c₂ :=
      GlobalState.Equiv.trans (splice_equiv (p := r.withOffset 40) (x := oY) heq₁) heq₂
    have c₃ :=
      GlobalState.Equiv.trans (splice_equiv (p := r.withOffset 120) (x := oZ) c₂) heq₃
    have hchain :=
      GlobalState.Equiv.trans (splice_equiv (p := r.withOffset 80) (x := oT) c₃) heq₄
    have halloc : u₄.alloc = s.alloc :=
      (heq₁.1.trans (heq₂.1.trans (heq₃.1.trans heq₄.1))).symm
    have hpop : (s.popFrame u₄.mem : GlobalState) ≈ u₄ :=
      GlobalState.Equiv.trans
        (killFrom_equiv_of_none (fun b hb => hu₄WF b (by rw [halloc]; omega)))
        ⟨halloc.symm, fun _ => rfl⟩
    exact GlobalState.Equiv.trans hchain (GlobalState.Equiv.symm hpop)

  case run =>
    denote_step_all v 3
    denote_eval v 0 3
    simp only [LLVM.const?] at hv0 hv1 hv2 hv3
    subst hv0 hv1 hv2 hv3

    refine (BlockCom.run_bind_denote_call_of_value
        (x := PoisonOr.value r) (s' := u₁) ?_).trans ?_
    · exact hrun₁

    denote_step_all v 5
    denote_eval v 5 5
    simp [gep, ptradd, LLVM.const?, LLVM.add, LLVM.mul, LLVM.add?, LLVM.mul?] at hv5
    have v5Value : v5 = .value (r.withOffset 40) := by
      simp [hv5, Pointer.withOffset, simp_sllvm]
    subst v5Value
    clear hv5

    refine (BlockCom.run_bind_denote_call_of_value
        (x := PoisonOr.value (r.withOffset 40)) (s' := u₂) ?_).trans ?_
    · exact hrun₂

    denote_step_all v 7
    denote_eval v 7 7
    simp [gep, ptradd, LLVM.const?, LLVM.add, LLVM.mul, LLVM.add?, LLVM.mul?] at hv7
    have v7Value : v7 = .value (r.withOffset 120) := by
      simp [hv7, Pointer.withOffset, simp_sllvm]
    subst v7Value
    clear hv7

    refine (BlockCom.run_bind_denote_call_of_value
        (x := PoisonOr.value (r.withOffset 120)) (s' := u₃) ?_).trans ?_
    · exact hrun₃

    denote_step_all v 9
    denote_eval v 9 9
    simp [gep, ptradd, LLVM.const?, LLVM.add, LLVM.mul, LLVM.add?, LLVM.mul?] at hv9
    have v9Value : v9 = .value (r.withOffset 80) := by
      simp [hv9, Pointer.withOffset, simp_sllvm]
    subst v9Value
    clear hv9

    refine (BlockCom.run_bind_denote_call_of_value
        (x := PoisonOr.value (r.withOffset 80)) (s' := u₄) ?_).trans ?_
    · exact hrun₄

    simp [BlockCom.denote_term, Terminator.denote_ret, simp_denote, simp_sllvm]

end Firedancer.Ref

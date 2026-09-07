import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_set_zero
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Memory
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Avx512.Proof.Common
import SSA.Projects.Firedancer.Avx512.Proof.Quad


namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

set_option maxHeartbeats 320000 in
set_option maxRecDepth 20000 in
theorem fd_ed25519_point_set_zero_conforms (p: Pointer) (s: GlobalState)
  (hs : s.WF)
  (hp : IsQuadPtr s.mem p) :
  fd_ed25519_point_set_zero_spec p s := by
    simp only [fd_ed25519_point_set_zero_spec, Cfg.denote]

    let result : Quad := ⟨#v[0, 1, 1, 0, 0, 0, 0, 0], #v[0, 0, 0, 0, 0, 0, 0, 0], #v[0, 0, 0, 0, 0, 0, 0, 0]⟩

    refine ⟨result, ?_, ?_, ?_, ?_⟩

    · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> intro i <;> fin_cases i <;> decide
    · subst result
      simp [Quad.toPoint, Quad.PointVecs, Quad.vector, quadElemVec, PointVectors.toPoint, decodeVec, Point.zero, Point.SamePoint]
    · subst result
      simp [Quad.toPoint, Quad.PointVecs, Quad.vector, quadElemVec, PointVectors.toPoint, decodeVec]

    let output_state : GlobalState :=
      { s with mem :=
          ((s.mem.splice p (vecBV result.v03)).splice
              (p.withOffset (64 : BitVec 64))
              (BitVec.replicate 128 (0#8))) }
    refine ⟨s.popFrame output_state.mem, ?_, ?_,⟩
    case refine_2 =>
      -- The gep lands 512 bits into the block: `IsQuadPtr`'s byte bound is what
      -- rules out the pointer wrapping around instead of stepping forward.
      have h64 : (64 : BitVec 64).toNat = 64 := rfl
      have hoff : (p.withOffset (64 : BitVec 64)).offsetInBits = p.offsetInBits + 512 := by
        have hb := hp.2
        simp only [Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add, h64] at hb ⊢
        omega
      -- Store then memset write exactly `result.BV`: `v14` and `v25` are the
      -- zeroed vectors that the 128 zero bytes flatten to.
      have hB : BitVec.replicate 128 (0#8) ++ vecBV result.v03 = result.BV := by
        rw [Quad.BV_append]
        show _ = 0#(512 * 0) ++ vecBV #v[0, 0, 0, 0, 0, 0, 0, 0]
          ++ vecBV #v[0, 0, 0, 0, 0, 0, 0, 0] ++ vecBV result.v03
        rw [vecBV_zero, zero_append_eq_replicate]
      let m₂ : MemoryState :=
        (s.mem.splice p (vecBV result.v03)).splice
          (p.withOffset (64 : BitVec 64)) (BitVec.replicate 128 (0#8))
      -- the two adjacent writes are one write of the whole QUAD
      have hadj : ({ s with mem := m₂ } : GlobalState)
          ≈ { s with mem := s.mem.splice p result.BV } := by
        rw [← hB]
        exact splice_splice_append_equiv _ _ hoff
      have hkill : (s.popFrame output_state.mem : GlobalState) ≈ output_state :=
        killFrom_equiv_of_none fun q hq =>
          live?_splice_eq_none (live?_splice_eq_none (hs q hq))
      exact GlobalState.Equiv.trans (GlobalState.Equiv.symm hadj)
        (GlobalState.Equiv.symm hkill)

    refine run_runFunction (s' := output_state) ?_

    denote_step_all v 4
    denote_eval v 0 4

    simp [LLVM.const?] at hv1 hv2 hv3 hv4
    subst hv1 hv2 hv3 hv4
    let z03 : Vector (BitVec 64) 8 := #v[0, 1, 1, 0, 0, 0, 0, 0]
    let z03' : Vector (LLVM.IntW 64) 8 := z03.map .value
    have hv0Value : v0 = z03' := by denote_dense hv0
    subst hv0Value
    clear hv0

    peel_store z03, p, hp.left, s

    set s₁ : GlobalState := { s with mem := s.mem.splice p (vecBV z03) } with hs₁
    have f₁ : Fits s₁.mem p (3 * 8 * 64) := fits_splice hp.left

    peel_gep 64 with p, f₁, s₁ as pField

    peel_memset (0#8), 128, pField, hpField, s₁
    simp_return

    simp [output_state, s₁]
    rfl

end Firedancer.Avx512

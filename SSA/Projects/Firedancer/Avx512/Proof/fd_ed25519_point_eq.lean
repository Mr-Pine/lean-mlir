import SSA.Projects.Firedancer.Avx512.Spec.fd_ed25519_point_eq
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Memory
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Avx512.Proof.Common
import SSA.Projects.Firedancer.Avx512.Proof.Quad
import SSA.Projects.Firedancer.Avx512.Proof.fd_r43x6_ge_is_eq


namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
theorem fd_ed25519_point_eq_conforms (p q: Pointer) (s: GlobalState)
  (hs : s.WF)
  (hp : IsQuadPtr s.mem p)
  (hq : IsQuadPtr s.mem q)
  (hpU46 : (readQuad hp).U46)
  (hqU46 : (readQuad hq).U46)
  (hpzUnit : IsUnit (readQuad hp).toPoint.Z)
  (hqzUnit : IsUnit (readQuad hq).toPoint.Z) :
  fd_ed25519_point_eq_spec p q s hp hq := by
    simp only [fd_ed25519_point_eq_spec, Cfg.denote]

    obtain ⟨eqstate, heqstate, heqstate_eq⟩ :=
      spec_run_fd_r43x6_ge_is_eq (readQuad hp) (readQuad hq) hpU46 hqU46 hpzUnit hqzUnit s hs

    refine ⟨s.popFrame eqstate.mem, run_runFunction (s' := eqstate) ?_, GlobalState.Equiv.symm
      (GlobalState.killFrom_equiv eqstate.mem hs fun b _ => heqstate_eq.2 b)⟩

    denote_step_all v 2
    denote_eval v 0 2
    simp only [LLVM.const?] at hv0 hv1 hv2
    subst hv0 hv1 hv2

    obtain ⟨pblk, hpblkE, hplen⟩ := hp.1
    have hplive : s.mem.live? p.id = some pblk := by simp [MemoryState.live?, hpblkE]
    obtain ⟨qblk, hqblkE, hqlen⟩ := hq.1
    have hqlive : s.mem.live? q.id = some qblk := by simp [MemoryState.live?, hqblkE]
    have h64 : (64 : BitVec 64).toNat = 64 := rfl
    have h128 : (128 : BitVec 64).toNat = 128 := rfl

    peel_load (.vector 8 (.bitvec (.concrete 64))), pblk, p, hpblkE, s
    rw [unflatten_readQuad_v03 hp hplive]

    peel_gep 64 with p, hp.1, s as pField
    have hoffP : pField.offsetInBits = p.offsetInBits + 512 := by
      have hb := hp.2
      simp only [pField, Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add, h64] at hb ⊢
      omega
    have hpFieldE : s.mem[pField.id]? = some (.live pblk) := hpblkE
    peel_load (.vector 8 (.bitvec (.concrete 64))), pblk, pField, hpFieldE, s
    rw [hoffP, unflatten_readQuad_v14 hp hplive]

    peel_gep 128 with p, hp.1, s as pField25
    have hoffP25 : pField25.offsetInBits = p.offsetInBits + 1024 := by
      have hb := hp.2
      simp only [pField25, Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add, h128] at hb ⊢
      omega
    have hpField25E : s.mem[pField25.id]? = some (.live pblk) := hpblkE
    peel_load (.vector 8 (.bitvec (.concrete 64))), pblk, pField25, hpField25E, s
    rw [hoffP25, unflatten_readQuad_v25 hp hplive]

    peel_load (.vector 8 (.bitvec (.concrete 64))), qblk, q, hqblkE, s
    rw [unflatten_readQuad_v03 hq hqlive]

    peel_gep 64 with q, hq.1, s as qField
    have hoffQ : qField.offsetInBits = q.offsetInBits + 512 := by
      have hb := hq.2
      simp only [qField, Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add, h64] at hb ⊢
      omega
    have hqFieldE : s.mem[qField.id]? = some (.live qblk) := hqblkE
    peel_load (.vector 8 (.bitvec (.concrete 64))), qblk, qField, hqFieldE, s
    rw [hoffQ, unflatten_readQuad_v14 hq hqlive]

    peel_gep 128 with q, hq.1, s as qField25
    have hoffQ25 : qField25.offsetInBits = q.offsetInBits + 1024 := by
      have hb := hq.2
      simp only [qField25, Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add, h128] at hb ⊢
      omega
    have hqField25E : s.mem[qField25.id]? = some (.live qblk) := hqblkE
    peel_load (.vector 8 (.bitvec (.concrete 64))), qblk, qField25, hqField25E, s
    rw [hoffQ25, unflatten_readQuad_v25 hq hqlive]

    peel_call heqstate
    simp_return

end Firedancer.Avx512

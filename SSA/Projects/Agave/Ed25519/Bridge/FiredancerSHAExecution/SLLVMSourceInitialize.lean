import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceInit
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM
open InstCombine (LLVM)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def initMemory (m : MemoryState) (p : Pointer) : MemoryState :=
  let m := m.splice (p.withOffset 128#64) (7640891576956012808#64)
  let m := m.splice (p.withOffset 136#64) (13503953896175478587#64)
  let m := m.splice (p.withOffset 144#64) (4354685564936845355#64)
  let m := m.splice (p.withOffset 152#64) (11912009170470909681#64)
  let m := m.splice (p.withOffset 160#64) (5840696475078001361#64)
  let m := m.splice (p.withOffset 168#64) (11170449401992604703#64)
  let m := m.splice (p.withOffset 176#64) (2270897969802886507#64)
  let m := m.splice (p.withOffset 184#64) (6620516959819538809#64)
  m.splice (p.withOffset 200#64) (0#192)

theorem init_body (p : Pointer) (s : GlobalState)
    (hr : Fits s.mem p (224 * 8)) :
    StateT.run (init.denote (Ctxt.Valuation.singleton (.value p))) s =
      .value ([.value p]ₕ, {s with mem := initMemory s.mem p}) := by
  simp only [Cfg.denote]
  denote_expose
  denote_step_all v 18
  denote_eval v 0 18
  simp only [LLVM.const?] at hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15 hv16 hv17 hv18
  have k0 : BitVec.ofInt 64 (128) = (128#64) := by decide
  rw [k0] at hv0
  have k1 : BitVec.ofInt 64 (7640891576956012808) = (7640891576956012808#64) := by decide
  rw [k1] at hv1
  have k2 : BitVec.ofInt 64 (136) = (136#64) := by decide
  rw [k2] at hv2
  have k3 : BitVec.ofInt 64 (-4942790177534073029) = (13503953896175478587#64) := by decide
  rw [k3] at hv3
  have k4 : BitVec.ofInt 64 (144) = (144#64) := by decide
  rw [k4] at hv4
  have k5 : BitVec.ofInt 64 (4354685564936845355) = (4354685564936845355#64) := by decide
  rw [k5] at hv5
  have k6 : BitVec.ofInt 64 (152) = (152#64) := by decide
  rw [k6] at hv6
  have k7 : BitVec.ofInt 64 (-6534734903238641935) = (11912009170470909681#64) := by decide
  rw [k7] at hv7
  have k8 : BitVec.ofInt 64 (160) = (160#64) := by decide
  rw [k8] at hv8
  have k9 : BitVec.ofInt 64 (5840696475078001361) = (5840696475078001361#64) := by decide
  rw [k9] at hv9
  have k10 : BitVec.ofInt 64 (168) = (168#64) := by decide
  rw [k10] at hv10
  have k11 : BitVec.ofInt 64 (-7276294671716946913) = (11170449401992604703#64) := by decide
  rw [k11] at hv11
  have k12 : BitVec.ofInt 64 (176) = (176#64) := by decide
  rw [k12] at hv12
  have k13 : BitVec.ofInt 64 (2270897969802886507) = (2270897969802886507#64) := by decide
  rw [k13] at hv13
  have k14 : BitVec.ofInt 64 (184) = (184#64) := by decide
  rw [k14] at hv14
  have k15 : BitVec.ofInt 64 (6620516959819538809) = (6620516959819538809#64) := by decide
  rw [k15] at hv15
  have k16 : BitVec.ofInt 64 (200) = (200#64) := by decide
  rw [k16] at hv16
  have k17 : BitVec.ofInt 8 (0) = (0#8) := by decide
  rw [k17] at hv17
  have k18 : BitVec.ofInt 64 (24) = (24#64) := by decide
  rw [k18] at hv18
  subst hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15 hv16 hv17 hv18
  peel_gep 128 with p, hr, s as ptr0
  peel_store (7640891576956012808#64), ptr0, hptr0, s
  obtain ⟨s1, hs1⟩ : ∃ t : GlobalState, {s with mem := s.mem.splice ptr0 (7640891576956012808#64)} = t := ⟨_, rfl⟩
  rw [hs1]
  have f1 : Fits s1.mem p (224 * 8) := hs1 ▸ fits_splice hr
  peel_gep 136 with p, f1, s1 as ptr1
  peel_store (13503953896175478587#64), ptr1, hptr1, s1
  obtain ⟨s2, hs2⟩ : ∃ t : GlobalState, {s1 with mem := s1.mem.splice ptr1 (13503953896175478587#64)} = t := ⟨_, rfl⟩
  rw [hs2]
  have f2 : Fits s2.mem p (224 * 8) := hs2 ▸ fits_splice f1
  peel_gep 144 with p, f2, s2 as ptr2
  peel_store (4354685564936845355#64), ptr2, hptr2, s2
  obtain ⟨s3, hs3⟩ : ∃ t : GlobalState, {s2 with mem := s2.mem.splice ptr2 (4354685564936845355#64)} = t := ⟨_, rfl⟩
  rw [hs3]
  have f3 : Fits s3.mem p (224 * 8) := hs3 ▸ fits_splice f2
  peel_gep 152 with p, f3, s3 as ptr3
  peel_store (11912009170470909681#64), ptr3, hptr3, s3
  obtain ⟨s4, hs4⟩ : ∃ t : GlobalState, {s3 with mem := s3.mem.splice ptr3 (11912009170470909681#64)} = t := ⟨_, rfl⟩
  rw [hs4]
  have f4 : Fits s4.mem p (224 * 8) := hs4 ▸ fits_splice f3
  peel_gep 160 with p, f4, s4 as ptr4
  peel_store (5840696475078001361#64), ptr4, hptr4, s4
  obtain ⟨s5, hs5⟩ : ∃ t : GlobalState, {s4 with mem := s4.mem.splice ptr4 (5840696475078001361#64)} = t := ⟨_, rfl⟩
  rw [hs5]
  have f5 : Fits s5.mem p (224 * 8) := hs5 ▸ fits_splice f4
  peel_gep 168 with p, f5, s5 as ptr5
  peel_store (11170449401992604703#64), ptr5, hptr5, s5
  obtain ⟨s6, hs6⟩ : ∃ t : GlobalState, {s5 with mem := s5.mem.splice ptr5 (11170449401992604703#64)} = t := ⟨_, rfl⟩
  rw [hs6]
  have f6 : Fits s6.mem p (224 * 8) := hs6 ▸ fits_splice f5
  peel_gep 176 with p, f6, s6 as ptr6
  peel_store (2270897969802886507#64), ptr6, hptr6, s6
  obtain ⟨s7, hs7⟩ : ∃ t : GlobalState, {s6 with mem := s6.mem.splice ptr6 (2270897969802886507#64)} = t := ⟨_, rfl⟩
  rw [hs7]
  have f7 : Fits s7.mem p (224 * 8) := hs7 ▸ fits_splice f6
  peel_gep 184 with p, f7, s7 as ptr7
  peel_store (6620516959819538809#64), ptr7, hptr7, s7
  obtain ⟨s8, hs8⟩ : ∃ t : GlobalState, {s7 with mem := s7.mem.splice ptr7 (6620516959819538809#64)} = t := ⟨_, rfl⟩
  rw [hs8]
  have f8 : Fits s8.mem p (224 * 8) := hs8 ▸ fits_splice f7
  peel_gep 200 with p, f8, s8 as tail
  peel_memset (0#8), 24, tail, htail, s8
  simp only [BlockCom.denote_term, Terminator.denote_ret, initMemory,
    ← hs1, ← hs2, ← hs3, ← hs4, ← hs5, ← hs6, ← hs7, ← hs8,
    ptr0, ptr1, ptr2, ptr3, ptr4, ptr5, ptr6, ptr7, tail, simp_denote, simp_sllvm]
  rfl

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource

import SSA.Projects.Agave.Ed25519.Bridge.CrossClientReachableConcrete
import SSA.Projects.Agave.Ed25519.Bridge.AgaveReadyEnvironmentWitnessCaller
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerEnvironmentReads

/-! Both actual clients in explicit loaded environments, for arbitrary caller
bytes. Only the external comparator, hardware instruction laws, and ordinary
message-size bound remain as hypotheses. The canonical-R policy is exact. -/
namespace Agave.Ed25519.Bridge.CrossClientLoaded
open Verifier Verifier.Execution Firedancer Firedancer.Common
open LeanMLIR.RIR (Vals EffectM)
open AgaveReady.EnvironmentWitness
open FiredancerSHAExecution
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 24000
set_option maxHeartbeats 1600000
attribute [local irreducible] callerState FiredancerEnvironmentWitness.initial
  AgaveReady.wrapper

noncomputable def agaveProgram
    (compareCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals [.bv 32]))
    (hardware : Dalek.Avx2Cache.Instructions.HardwareInstructions)
    (panic : DoubleBase.RIR.SerialPanic)
    (avx2Panic : Vals [.bv 64, .bv 64, .ptr] → EffectM (Vals [])) :=
  Wrapper.program (AgaveReady.wrapper (AgaveReady.bcmpOnly compareCall) dg hardware
    serial d2 panic avx2Panic avx cg sg scg ddg dsg)

def firedancerState (a r s : Bytes32) (message : List (BitVec 8)) : LeanMLIR.GlobalState :=
  FiredancerEnvironmentWitness.initial (FiredancerEnvironmentWitness.packMessage message) (s ++ r) a

section
variable (compareCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals [.bv 32]))
variable (hardware : Dalek.Avx2Cache.Instructions.HardwareInstructions)
variable (panic : DoubleBase.RIR.SerialPanic)
variable (avx2Panic : Vals [.bv 64, .bv 64, .ptr] → EffectM (Vals []))
variable (hhardware : Dalek.Avx2Cache.Instructions.InstructionContracts hardware)
variable (hbcmp : Dalek.CompareContract compareCall)
variable (a r s : Bytes32) (message : List (BitVec 8))
variable (hlen : message.length < 2^63)
include hhardware hbcmp hlen

/-- Defined executions of both imported implementations on the same arbitrary
original bytes. No memory, table, hash, or execution premise is supplied. -/
theorem runs :
    ∃ (agaveFinal : LeanMLIR.RIR.GlobalState) (fdFinal : LeanMLIR.GlobalState)
      (b : Bool) (ret : BitVec 32),
      (agaveProgram compareCall hardware panic avx2Panic).call
        (invocation message).args (callerState a r s message) =
          .value (Wrapper.boolResult b, agaveFinal) ∧
      firedancerRun SLLVMSource.programs (FiredancerEnvironmentWitness.ptr 10)
        (BitVec.ofNat 64 message.length) (FiredancerEnvironmentWitness.ptr 11)
        (FiredancerEnvironmentWitness.ptr 12)
        (firedancerFreshSha (firedancerState a r s message))
        (firedancerWithSha (firedancerState a r s message)) =
          .value ([.value ret]ₕ, fdFinal) ∧
      b = (decide (ret = FD_ED25519_SUCCESS) && decide (CanonicalY r)) := by
  have hinput := FiredancerEnvironmentWitness.input
    (FiredancerEnvironmentWitness.packMessage message) (s ++ r) a hlen
  have hwf := FiredancerEnvironmentWitness.wf
    (FiredancerEnvironmentWitness.packMessage message) (s ++ r) a
  have hsmall := FiredancerEnvironmentWitness.small
    (FiredancerEnvironmentWitness.packMessage message) (s ++ r) a hlen
  have ha : readBuf (hinput.args hwf).pkBuf = a :=
    FiredancerEnvironmentWitness.read_key
      (FiredancerEnvironmentWitness.packMessage message) (s ++ r) a hlen
  have hr : readBuf (hinput.args hwf).sigBuf = r :=
    FiredancerEnvironmentWitness.read_r_split
      (FiredancerEnvironmentWitness.packMessage message) r s a hlen
  have hs : readBuf (hinput.args hwf).sBuf = s :=
    FiredancerEnvironmentWitness.read_s_split
      (FiredancerEnvironmentWitness.packMessage message) r s a hlen
  have hm : bytesOf (readWord (hinput.args hwf).msgFits) = message :=
    FiredancerEnvironmentWitness.read_message_list message r s a hlen
  have hcaller : ColdInput.CallerMemory (invocation message) (callerState a r s message)
      (readBuf (hinput.args hwf).pkBuf) (readBuf (hinput.args hwf).sigBuf)
      (readBuf (hinput.args hwf).sBuf) (bytesOf (readWord (hinput.args hwf).msgFits)) := by
    rw [ha, hr, hs, hm]
    exact caller_memory a r s message hlen
  have hrun := CrossClientReachableConcrete.runs compareCall dg hardware serial d2 panic
    avx2Panic avx cg sg scg ddg dsg hhardware hbcmp
    (invocation message) (callerState a r s message)
    (firedancerState a r s message) (FiredancerEnvironmentWitness.ptr 10)
    (BitVec.ofNat 64 message.length) (FiredancerEnvironmentWitness.ptr 11)
    (FiredancerEnvironmentWitness.ptr 12) hinput hwf
    (FiredancerEnvironmentWitness.fields _ _ _)
    (FiredancerEnvironmentWitness.ptr 9) (FiredancerEnvironmentWitness.sha _ _ _)
    (FiredancerEnvironmentWitness.ptr 8) (FiredancerEnvironmentWitness.base _ _ _)
    hsmall.1 hsmall.2.1 hsmall.2.2 hcaller
    (caller_initialized a r s message) (caller_serial_ready a r s message)
    (caller_avx_ready a r s message) serial_separate avx_separate
  obtain ⟨af, ff, b, ret, hagave, hfd, hb⟩ := hrun
  refine ⟨af, ff, b, ret, hagave, hfd, ?_⟩
  change b = (decide (ret = FD_ED25519_SUCCESS) &&
    decide (CanonicalY (readBuf (hinput.args hwf).sigBuf))) at hb
  rw [hr] at hb
  exact hb

/-- On canonical R, the actual returned acceptance decisions agree. -/
theorem runs_of_canonical (hcanonical : CanonicalY r) :
    ∃ (agaveFinal : LeanMLIR.RIR.GlobalState) (fdFinal : LeanMLIR.GlobalState)
      (b : Bool) (ret : BitVec 32),
      (agaveProgram compareCall hardware panic avx2Panic).call
        (invocation message).args (callerState a r s message) =
          .value (Wrapper.boolResult b, agaveFinal) ∧
      firedancerRun SLLVMSource.programs (FiredancerEnvironmentWitness.ptr 10)
        (BitVec.ofNat 64 message.length) (FiredancerEnvironmentWitness.ptr 11)
        (FiredancerEnvironmentWitness.ptr 12)
        (firedancerFreshSha (firedancerState a r s message))
        (firedancerWithSha (firedancerState a r s message)) =
          .value ([.value ret]ₕ, fdFinal) ∧
      b = decide (ret = FD_ED25519_SUCCESS) := by
  obtain ⟨af, ff, b, ret, ha, hf, hb⟩ :=
    runs compareCall hardware panic avx2Panic hhardware hbcmp a r s message hlen
  exact ⟨af, ff, b, ret, ha, hf, by simpa only [hcanonical, decide_true, Bool.and_true] using hb⟩

end
end Agave.Ed25519.Bridge.CrossClientLoaded

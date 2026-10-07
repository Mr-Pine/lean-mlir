import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InvocationReturn

/-! Compose all 607 exact imported wrapper instructions without a phase premise. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

theorem invocation_body_run (g : Globals) (E : Env program.Γ) (state : GlobalState)
    (out input : Pointer) (bytes : BitVec 512)
    (hwf : state.WF) (hr : Ready g state out)
    (harg0 : E.read (%arg0) = .value out) (harg1 : E.read (%arg1) = .value input)
    (hout : SmallRange state.mem out 32) (hin : SmallRange state.mem input 64)
    (hread : state.mem.readAt input 512 = bytes) :
    (program.entry linkedPrimitives g).runBodyFrom E 0 state =
      .value (returnEnv E g state out input bytes, returnState g state out input bytes) := by
  rw [invocation_split_run linkedPrimitives g E state input bytes hwf harg1 hin hread]
  rw [invocation_calls_run g E state out input bytes hwf hr]
  rw [invocation_sum_run g E state input bytes]
  rw [invocation_result_run g E state input bytes hwf]
  rw [invocation_inputCleanup_run g E state input bytes]
  rw [invocation_serialize_run g E state input bytes]
  rw [invocation_byteStores_run g E state out input bytes hwf harg0 hout]
  exact invocation_finalCleanup_run g E state out input bytes

end Agave.Ed25519.Verifier.Execution.ScalarWide

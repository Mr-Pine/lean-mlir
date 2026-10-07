import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InvocationBody

/-! Full linked wide-reduction call, with the two exact immutable global
initializers as invocation-local assumptions. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
open Agave.Ed25519.Verifier.Execution.Dalek (args2 ReadBytes)
set_option maxRecDepth 100000

/-- The actual complete call with exact memory, counter, and canonical output. -/
theorem linked_program_call (g : Globals) (out input : Pointer) (state : GlobalState)
    (bytes : BitVec 512) (hwf : state.WF) (hr : Ready g state out)
    (hout : SmallRange state.mem out 32) (hin : ReadBytes state input 64 bytes) :
    (linkedProgram g).call (args2 out input) state =
      .value (.nil, exactPostState state out bytes) := by
  let args := args2 out input
  let E : Env program.Γ := Env.init args.get
  let ef := returnEnv E g state out input bytes
  let sf := returnState g state out input bytes
  have hbody := invocation_body_run g E state out input bytes hwf hr rfl rfl hout hin.1 hin.2
  have hblock : (program.entry linkedPrimitives g).run program.blockParams E state =
      .value ((ef, .inl .nil), sf) := by
    rw [BasicBlock.run_eq]
    simp only [EffectM.bind_eq, hbody, LeanMLIR.RIR.PoisonOr.value_bind]
    rfl
  have hrun : (program linkedPrimitives g).run args state = .value (.nil, sf) := by
    rw [Func.run_runFrom_eq, Func.runFrom_eq]
    change (do
      let ((E', res), s') ← (program.entry linkedPrimitives g).run program.blockParams E state
      Func.continue («func» := program linkedPrimitives g) E' res s') = _
    rw [hblock]
    rfl
  have hpost := returnState_post g state out input bytes hwf hout
  have hcall := Func.call_of_run hrun
  simpa only [linkedProgram, args, sf, hpost] using hcall

/-- Inhabit the declared exact ABI contract from the actual composed body. -/
theorem execution_obligation (g : Globals) : ExecutionObligation g := by
  intro out input state bytes hwf hr hout hin _hdisjoint
  exact linked_program_call g out input state bytes hwf hr hout hin

end Agave.Ed25519.Verifier.Execution.ScalarWide

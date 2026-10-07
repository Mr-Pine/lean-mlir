import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullWorkState
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound56
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound57
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound58
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound59
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound60
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound61
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound62
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound63

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Spec

theorem full_segment07 (E : Env program.Γ) (state : GlobalState)
    (initial : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready56 E (workState initial w 56) w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', program.bb4.runBodyFrom E 2027 state =
      program.bb4.runBodyFrom E' 2339 state ∧
      Ready64 E' (workState initial w 64) w ∧ Constants E' kp ∧ Frame E E' := by
  obtain ⟨E57, hb56, h57, hc57, hf56⟩ := full_step56 E state (workState initial w 56) w kp h hc hw hk
  change Ready57 E57 (workState initial w 57) w at h57
  have hr56 := runBodyFrom_slice E E57 2027 39 state hb56
  change program.bb4.runBodyFrom E 2027 state = program.bb4.runBodyFrom E57 2066 state at hr56
  obtain ⟨E58, hb57, h58, hc58, hf57⟩ := full_step57 E57 state (workState initial w 57) w kp h57 hc57 hw hk
  change Ready58 E58 (workState initial w 58) w at h58
  have hr57 := runBodyFrom_slice E57 E58 2066 39 state hb57
  change program.bb4.runBodyFrom E57 2066 state = program.bb4.runBodyFrom E58 2105 state at hr57
  obtain ⟨E59, hb58, h59, hc59, hf58⟩ := full_step58 E58 state (workState initial w 58) w kp h58 hc58 hw hk
  change Ready59 E59 (workState initial w 59) w at h59
  have hr58 := runBodyFrom_slice E58 E59 2105 39 state hb58
  change program.bb4.runBodyFrom E58 2105 state = program.bb4.runBodyFrom E59 2144 state at hr58
  obtain ⟨E60, hb59, h60, hc60, hf59⟩ := full_step59 E59 state (workState initial w 59) w kp h59 hc59 hw hk
  change Ready60 E60 (workState initial w 60) w at h60
  have hr59 := runBodyFrom_slice E59 E60 2144 39 state hb59
  change program.bb4.runBodyFrom E59 2144 state = program.bb4.runBodyFrom E60 2183 state at hr59
  obtain ⟨E61, hb60, h61, hc61, hf60⟩ := full_step60 E60 state (workState initial w 60) w kp h60 hc60 hw hk
  change Ready61 E61 (workState initial w 61) w at h61
  have hr60 := runBodyFrom_slice E60 E61 2183 39 state hb60
  change program.bb4.runBodyFrom E60 2183 state = program.bb4.runBodyFrom E61 2222 state at hr60
  obtain ⟨E62, hb61, h62, hc62, hf61⟩ := full_step61 E61 state (workState initial w 61) w kp h61 hc61 hw hk
  change Ready62 E62 (workState initial w 62) w at h62
  have hr61 := runBodyFrom_slice E61 E62 2222 39 state hb61
  change program.bb4.runBodyFrom E61 2222 state = program.bb4.runBodyFrom E62 2261 state at hr61
  obtain ⟨E63, hb62, h63, hc63, hf62⟩ := full_step62 E62 state (workState initial w 62) w kp h62 hc62 hw hk
  change Ready63 E63 (workState initial w 63) w at h63
  have hr62 := runBodyFrom_slice E62 E63 2261 39 state hb62
  change program.bb4.runBodyFrom E62 2261 state = program.bb4.runBodyFrom E63 2300 state at hr62
  obtain ⟨E64, hb63, h64, hc64, hf63⟩ := full_step63 E63 state (workState initial w 63) w kp h63 hc63 hw hk
  change Ready64 E64 (workState initial w 64) w at h64
  have hr63 := runBodyFrom_slice E63 E64 2300 39 state hb63
  change program.bb4.runBodyFrom E63 2300 state = program.bb4.runBodyFrom E64 2339 state at hr63
  refine ⟨E64, ?_, h64, hc64, (((((((hf56).trans hf57).trans hf58).trans hf59).trans hf60).trans hf61).trans hf62).trans hf63⟩
  exact (((((((hr56).trans hr57).trans hr58).trans hr59).trans hr60).trans hr61).trans hr62).trans hr63

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull

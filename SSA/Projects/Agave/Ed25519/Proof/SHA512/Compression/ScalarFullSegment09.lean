import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullWorkState
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound72
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound73
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound74
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound75
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound76
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound77
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound78

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Spec

theorem full_segment09 (E : Env program.Γ) (state : GlobalState)
    (initial : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready72 E (workState initial w 72) w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', program.bb4.runBodyFrom E 2651 state =
      program.bb4.runBodyFrom E' 2924 state ∧
      Ready79 E' (workState initial w 79) w ∧ Constants E' kp ∧ Frame E E' := by
  obtain ⟨E73, hb72, h73, hc73, hf72⟩ := full_step72 E state (workState initial w 72) w kp h hc hw hk
  change Ready73 E73 (workState initial w 73) w at h73
  have hr72 := runBodyFrom_slice E E73 2651 39 state hb72
  change program.bb4.runBodyFrom E 2651 state = program.bb4.runBodyFrom E73 2690 state at hr72
  obtain ⟨E74, hb73, h74, hc74, hf73⟩ := full_step73 E73 state (workState initial w 73) w kp h73 hc73 hw hk
  change Ready74 E74 (workState initial w 74) w at h74
  have hr73 := runBodyFrom_slice E73 E74 2690 39 state hb73
  change program.bb4.runBodyFrom E73 2690 state = program.bb4.runBodyFrom E74 2729 state at hr73
  obtain ⟨E75, hb74, h75, hc75, hf74⟩ := full_step74 E74 state (workState initial w 74) w kp h74 hc74 hw hk
  change Ready75 E75 (workState initial w 75) w at h75
  have hr74 := runBodyFrom_slice E74 E75 2729 39 state hb74
  change program.bb4.runBodyFrom E74 2729 state = program.bb4.runBodyFrom E75 2768 state at hr74
  obtain ⟨E76, hb75, h76, hc76, hf75⟩ := full_step75 E75 state (workState initial w 75) w kp h75 hc75 hw hk
  change Ready76 E76 (workState initial w 76) w at h76
  have hr75 := runBodyFrom_slice E75 E76 2768 39 state hb75
  change program.bb4.runBodyFrom E75 2768 state = program.bb4.runBodyFrom E76 2807 state at hr75
  obtain ⟨E77, hb76, h77, hc77, hf76⟩ := full_step76 E76 state (workState initial w 76) w kp h76 hc76 hw hk
  change Ready77 E77 (workState initial w 77) w at h77
  have hr76 := runBodyFrom_slice E76 E77 2807 39 state hb76
  change program.bb4.runBodyFrom E76 2807 state = program.bb4.runBodyFrom E77 2846 state at hr76
  obtain ⟨E78, hb77, h78, hc78, hf77⟩ := full_step77 E77 state (workState initial w 77) w kp h77 hc77 hw hk
  change Ready78 E78 (workState initial w 78) w at h78
  have hr77 := runBodyFrom_slice E77 E78 2846 39 state hb77
  change program.bb4.runBodyFrom E77 2846 state = program.bb4.runBodyFrom E78 2885 state at hr77
  obtain ⟨E79, hb78, h79, hc79, hf78⟩ := full_step78 E78 state (workState initial w 78) w kp h78 hc78 hw hk
  change Ready79 E79 (workState initial w 79) w at h79
  have hr78 := runBodyFrom_slice E78 E79 2885 39 state hb78
  change program.bb4.runBodyFrom E78 2885 state = program.bb4.runBodyFrom E79 2924 state at hr78
  refine ⟨E79, ?_, h79, hc79, ((((((hf72).trans hf73).trans hf74).trans hf75).trans hf76).trans hf77).trans hf78⟩
  exact ((((((hr72).trans hr73).trans hr74).trans hr75).trans hr76).trans hr77).trans hr78

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull

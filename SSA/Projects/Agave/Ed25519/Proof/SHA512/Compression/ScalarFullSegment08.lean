import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullWorkState
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound64
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound65
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound66
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound67
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound68
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound69
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound70
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound71

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Spec

theorem full_segment08 (E : Env program.Γ) (state : GlobalState)
    (initial : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready64 E (workState initial w 64) w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', program.bb4.runBodyFrom E 2339 state =
      program.bb4.runBodyFrom E' 2651 state ∧
      Ready72 E' (workState initial w 72) w ∧ Constants E' kp ∧ Frame E E' := by
  obtain ⟨E65, hb64, h65, hc65, hf64⟩ := full_step64 E state (workState initial w 64) w kp h hc hw hk
  change Ready65 E65 (workState initial w 65) w at h65
  have hr64 := runBodyFrom_slice E E65 2339 39 state hb64
  change program.bb4.runBodyFrom E 2339 state = program.bb4.runBodyFrom E65 2378 state at hr64
  obtain ⟨E66, hb65, h66, hc66, hf65⟩ := full_step65 E65 state (workState initial w 65) w kp h65 hc65 hw hk
  change Ready66 E66 (workState initial w 66) w at h66
  have hr65 := runBodyFrom_slice E65 E66 2378 39 state hb65
  change program.bb4.runBodyFrom E65 2378 state = program.bb4.runBodyFrom E66 2417 state at hr65
  obtain ⟨E67, hb66, h67, hc67, hf66⟩ := full_step66 E66 state (workState initial w 66) w kp h66 hc66 hw hk
  change Ready67 E67 (workState initial w 67) w at h67
  have hr66 := runBodyFrom_slice E66 E67 2417 39 state hb66
  change program.bb4.runBodyFrom E66 2417 state = program.bb4.runBodyFrom E67 2456 state at hr66
  obtain ⟨E68, hb67, h68, hc68, hf67⟩ := full_step67 E67 state (workState initial w 67) w kp h67 hc67 hw hk
  change Ready68 E68 (workState initial w 68) w at h68
  have hr67 := runBodyFrom_slice E67 E68 2456 39 state hb67
  change program.bb4.runBodyFrom E67 2456 state = program.bb4.runBodyFrom E68 2495 state at hr67
  obtain ⟨E69, hb68, h69, hc69, hf68⟩ := full_step68 E68 state (workState initial w 68) w kp h68 hc68 hw hk
  change Ready69 E69 (workState initial w 69) w at h69
  have hr68 := runBodyFrom_slice E68 E69 2495 39 state hb68
  change program.bb4.runBodyFrom E68 2495 state = program.bb4.runBodyFrom E69 2534 state at hr68
  obtain ⟨E70, hb69, h70, hc70, hf69⟩ := full_step69 E69 state (workState initial w 69) w kp h69 hc69 hw hk
  change Ready70 E70 (workState initial w 70) w at h70
  have hr69 := runBodyFrom_slice E69 E70 2534 39 state hb69
  change program.bb4.runBodyFrom E69 2534 state = program.bb4.runBodyFrom E70 2573 state at hr69
  obtain ⟨E71, hb70, h71, hc71, hf70⟩ := full_step70 E70 state (workState initial w 70) w kp h70 hc70 hw hk
  change Ready71 E71 (workState initial w 71) w at h71
  have hr70 := runBodyFrom_slice E70 E71 2573 39 state hb70
  change program.bb4.runBodyFrom E70 2573 state = program.bb4.runBodyFrom E71 2612 state at hr70
  obtain ⟨E72, hb71, h72, hc72, hf71⟩ := full_step71 E71 state (workState initial w 71) w kp h71 hc71 hw hk
  change Ready72 E72 (workState initial w 72) w at h72
  have hr71 := runBodyFrom_slice E71 E72 2612 39 state hb71
  change program.bb4.runBodyFrom E71 2612 state = program.bb4.runBodyFrom E72 2651 state at hr71
  refine ⟨E72, ?_, h72, hc72, (((((((hf64).trans hf65).trans hf66).trans hf67).trans hf68).trans hf69).trans hf70).trans hf71⟩
  exact (((((((hr64).trans hr65).trans hr66).trans hr67).trans hr68).trans hr69).trans hr70).trans hr71

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull

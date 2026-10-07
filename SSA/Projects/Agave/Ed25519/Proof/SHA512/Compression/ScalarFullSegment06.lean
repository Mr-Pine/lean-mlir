import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullWorkState
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound48
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound49
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound50
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound51
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound52
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound53
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound54
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound55

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Spec

theorem full_segment06 (E : Env program.Γ) (state : GlobalState)
    (initial : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready48 E (workState initial w 48) w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', program.bb4.runBodyFrom E 1715 state =
      program.bb4.runBodyFrom E' 2027 state ∧
      Ready56 E' (workState initial w 56) w ∧ Constants E' kp ∧ Frame E E' := by
  obtain ⟨E49, hb48, h49, hc49, hf48⟩ := full_step48 E state (workState initial w 48) w kp h hc hw hk
  change Ready49 E49 (workState initial w 49) w at h49
  have hr48 := runBodyFrom_slice E E49 1715 39 state hb48
  change program.bb4.runBodyFrom E 1715 state = program.bb4.runBodyFrom E49 1754 state at hr48
  obtain ⟨E50, hb49, h50, hc50, hf49⟩ := full_step49 E49 state (workState initial w 49) w kp h49 hc49 hw hk
  change Ready50 E50 (workState initial w 50) w at h50
  have hr49 := runBodyFrom_slice E49 E50 1754 39 state hb49
  change program.bb4.runBodyFrom E49 1754 state = program.bb4.runBodyFrom E50 1793 state at hr49
  obtain ⟨E51, hb50, h51, hc51, hf50⟩ := full_step50 E50 state (workState initial w 50) w kp h50 hc50 hw hk
  change Ready51 E51 (workState initial w 51) w at h51
  have hr50 := runBodyFrom_slice E50 E51 1793 39 state hb50
  change program.bb4.runBodyFrom E50 1793 state = program.bb4.runBodyFrom E51 1832 state at hr50
  obtain ⟨E52, hb51, h52, hc52, hf51⟩ := full_step51 E51 state (workState initial w 51) w kp h51 hc51 hw hk
  change Ready52 E52 (workState initial w 52) w at h52
  have hr51 := runBodyFrom_slice E51 E52 1832 39 state hb51
  change program.bb4.runBodyFrom E51 1832 state = program.bb4.runBodyFrom E52 1871 state at hr51
  obtain ⟨E53, hb52, h53, hc53, hf52⟩ := full_step52 E52 state (workState initial w 52) w kp h52 hc52 hw hk
  change Ready53 E53 (workState initial w 53) w at h53
  have hr52 := runBodyFrom_slice E52 E53 1871 39 state hb52
  change program.bb4.runBodyFrom E52 1871 state = program.bb4.runBodyFrom E53 1910 state at hr52
  obtain ⟨E54, hb53, h54, hc54, hf53⟩ := full_step53 E53 state (workState initial w 53) w kp h53 hc53 hw hk
  change Ready54 E54 (workState initial w 54) w at h54
  have hr53 := runBodyFrom_slice E53 E54 1910 39 state hb53
  change program.bb4.runBodyFrom E53 1910 state = program.bb4.runBodyFrom E54 1949 state at hr53
  obtain ⟨E55, hb54, h55, hc55, hf54⟩ := full_step54 E54 state (workState initial w 54) w kp h54 hc54 hw hk
  change Ready55 E55 (workState initial w 55) w at h55
  have hr54 := runBodyFrom_slice E54 E55 1949 39 state hb54
  change program.bb4.runBodyFrom E54 1949 state = program.bb4.runBodyFrom E55 1988 state at hr54
  obtain ⟨E56, hb55, h56, hc56, hf55⟩ := full_step55 E55 state (workState initial w 55) w kp h55 hc55 hw hk
  change Ready56 E56 (workState initial w 56) w at h56
  have hr55 := runBodyFrom_slice E55 E56 1988 39 state hb55
  change program.bb4.runBodyFrom E55 1988 state = program.bb4.runBodyFrom E56 2027 state at hr55
  refine ⟨E56, ?_, h56, hc56, (((((((hf48).trans hf49).trans hf50).trans hf51).trans hf52).trans hf53).trans hf54).trans hf55⟩
  exact (((((((hr48).trans hr49).trans hr50).trans hr51).trans hr52).trans hr53).trans hr54).trans hr55

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull

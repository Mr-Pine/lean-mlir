import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullWorkState
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound24
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound25
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound26
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound27
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound28
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound29
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound30
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound31

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Spec

theorem full_segment03 (E : Env program.Γ) (state : GlobalState)
    (initial : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready24 E (workState initial w 24) w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', program.bb4.runBodyFrom E 779 state =
      program.bb4.runBodyFrom E' 1091 state ∧
      Ready32 E' (workState initial w 32) w ∧ Constants E' kp ∧ Frame E E' := by
  obtain ⟨E25, hb24, h25, hc25, hf24⟩ := full_step24 E state (workState initial w 24) w kp h hc hw hk
  change Ready25 E25 (workState initial w 25) w at h25
  have hr24 := runBodyFrom_slice E E25 779 39 state hb24
  change program.bb4.runBodyFrom E 779 state = program.bb4.runBodyFrom E25 818 state at hr24
  obtain ⟨E26, hb25, h26, hc26, hf25⟩ := full_step25 E25 state (workState initial w 25) w kp h25 hc25 hw hk
  change Ready26 E26 (workState initial w 26) w at h26
  have hr25 := runBodyFrom_slice E25 E26 818 39 state hb25
  change program.bb4.runBodyFrom E25 818 state = program.bb4.runBodyFrom E26 857 state at hr25
  obtain ⟨E27, hb26, h27, hc27, hf26⟩ := full_step26 E26 state (workState initial w 26) w kp h26 hc26 hw hk
  change Ready27 E27 (workState initial w 27) w at h27
  have hr26 := runBodyFrom_slice E26 E27 857 39 state hb26
  change program.bb4.runBodyFrom E26 857 state = program.bb4.runBodyFrom E27 896 state at hr26
  obtain ⟨E28, hb27, h28, hc28, hf27⟩ := full_step27 E27 state (workState initial w 27) w kp h27 hc27 hw hk
  change Ready28 E28 (workState initial w 28) w at h28
  have hr27 := runBodyFrom_slice E27 E28 896 39 state hb27
  change program.bb4.runBodyFrom E27 896 state = program.bb4.runBodyFrom E28 935 state at hr27
  obtain ⟨E29, hb28, h29, hc29, hf28⟩ := full_step28 E28 state (workState initial w 28) w kp h28 hc28 hw hk
  change Ready29 E29 (workState initial w 29) w at h29
  have hr28 := runBodyFrom_slice E28 E29 935 39 state hb28
  change program.bb4.runBodyFrom E28 935 state = program.bb4.runBodyFrom E29 974 state at hr28
  obtain ⟨E30, hb29, h30, hc30, hf29⟩ := full_step29 E29 state (workState initial w 29) w kp h29 hc29 hw hk
  change Ready30 E30 (workState initial w 30) w at h30
  have hr29 := runBodyFrom_slice E29 E30 974 39 state hb29
  change program.bb4.runBodyFrom E29 974 state = program.bb4.runBodyFrom E30 1013 state at hr29
  obtain ⟨E31, hb30, h31, hc31, hf30⟩ := full_step30 E30 state (workState initial w 30) w kp h30 hc30 hw hk
  change Ready31 E31 (workState initial w 31) w at h31
  have hr30 := runBodyFrom_slice E30 E31 1013 39 state hb30
  change program.bb4.runBodyFrom E30 1013 state = program.bb4.runBodyFrom E31 1052 state at hr30
  obtain ⟨E32, hb31, h32, hc32, hf31⟩ := full_step31 E31 state (workState initial w 31) w kp h31 hc31 hw hk
  change Ready32 E32 (workState initial w 32) w at h32
  have hr31 := runBodyFrom_slice E31 E32 1052 39 state hb31
  change program.bb4.runBodyFrom E31 1052 state = program.bb4.runBodyFrom E32 1091 state at hr31
  refine ⟨E32, ?_, h32, hc32, (((((((hf24).trans hf25).trans hf26).trans hf27).trans hf28).trans hf29).trans hf30).trans hf31⟩
  exact (((((((hr24).trans hr25).trans hr26).trans hr27).trans hr28).trans hr29).trans hr30).trans hr31

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull

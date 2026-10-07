import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullWorkState
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound00
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound01
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound02
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound03
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound04
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound05
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound06
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound07

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Spec

theorem full_segment00 (E : Env program.Γ) (state : GlobalState)
    (initial : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready00 E (workState initial w 0) w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', program.bb4.runBodyFrom E 50 state =
      program.bb4.runBodyFrom E' 259 state ∧
      Ready08 E' (workState initial w 8) w ∧ Constants E' kp ∧ Frame E E' := by
  obtain ⟨E1, hb0, h1, hc1, hf0⟩ := full_step00 E state (workState initial w 0) w kp h hc hw hk
  change Ready01 E1 (workState initial w 1) w at h1
  have hr0 := runBodyFrom_slice E E1 50 27 state hb0
  change program.bb4.runBodyFrom E 50 state = program.bb4.runBodyFrom E1 77 state at hr0
  obtain ⟨E2, hb1, h2, hc2, hf1⟩ := full_step01 E1 state (workState initial w 1) w kp h1 hc1 hw hk
  change Ready02 E2 (workState initial w 2) w at h2
  have hr1 := runBodyFrom_slice E1 E2 77 26 state hb1
  change program.bb4.runBodyFrom E1 77 state = program.bb4.runBodyFrom E2 103 state at hr1
  obtain ⟨E3, hb2, h3, hc3, hf2⟩ := full_step02 E2 state (workState initial w 2) w kp h2 hc2 hw hk
  change Ready03 E3 (workState initial w 3) w at h3
  have hr2 := runBodyFrom_slice E2 E3 103 26 state hb2
  change program.bb4.runBodyFrom E2 103 state = program.bb4.runBodyFrom E3 129 state at hr2
  obtain ⟨E4, hb3, h4, hc4, hf3⟩ := full_step03 E3 state (workState initial w 3) w kp h3 hc3 hw hk
  change Ready04 E4 (workState initial w 4) w at h4
  have hr3 := runBodyFrom_slice E3 E4 129 26 state hb3
  change program.bb4.runBodyFrom E3 129 state = program.bb4.runBodyFrom E4 155 state at hr3
  obtain ⟨E5, hb4, h5, hc5, hf4⟩ := full_step04 E4 state (workState initial w 4) w kp h4 hc4 hw hk
  change Ready05 E5 (workState initial w 5) w at h5
  have hr4 := runBodyFrom_slice E4 E5 155 26 state hb4
  change program.bb4.runBodyFrom E4 155 state = program.bb4.runBodyFrom E5 181 state at hr4
  obtain ⟨E6, hb5, h6, hc6, hf5⟩ := full_step05 E5 state (workState initial w 5) w kp h5 hc5 hw hk
  change Ready06 E6 (workState initial w 6) w at h6
  have hr5 := runBodyFrom_slice E5 E6 181 26 state hb5
  change program.bb4.runBodyFrom E5 181 state = program.bb4.runBodyFrom E6 207 state at hr5
  obtain ⟨E7, hb6, h7, hc7, hf6⟩ := full_step06 E6 state (workState initial w 6) w kp h6 hc6 hw hk
  change Ready07 E7 (workState initial w 7) w at h7
  have hr6 := runBodyFrom_slice E6 E7 207 26 state hb6
  change program.bb4.runBodyFrom E6 207 state = program.bb4.runBodyFrom E7 233 state at hr6
  obtain ⟨E8, hb7, h8, hc8, hf7⟩ := full_step07 E7 state (workState initial w 7) w kp h7 hc7 hw hk
  change Ready08 E8 (workState initial w 8) w at h8
  have hr7 := runBodyFrom_slice E7 E8 233 26 state hb7
  change program.bb4.runBodyFrom E7 233 state = program.bb4.runBodyFrom E8 259 state at hr7
  refine ⟨E8, ?_, h8, hc8, (((((((hf0).trans hf1).trans hf2).trans hf3).trans hf4).trans hf5).trans hf6).trans hf7⟩
  exact (((((((hr0).trans hr1).trans hr2).trans hr3).trans hr4).trans hr5).trans hr6).trans hr7

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull

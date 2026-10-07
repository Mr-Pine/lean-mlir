import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullWorkState
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound08
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound09
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound10
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound11
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound12
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound13
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound14
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound15

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Spec

theorem full_segment01 (E : Env program.Γ) (state : GlobalState)
    (initial : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready08 E (workState initial w 8) w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', program.bb4.runBodyFrom E 259 state =
      program.bb4.runBodyFrom E' 467 state ∧
      Ready16 E' (workState initial w 16) w ∧ Constants E' kp ∧ Frame E E' := by
  obtain ⟨E9, hb8, h9, hc9, hf8⟩ := full_step08 E state (workState initial w 8) w kp h hc hw hk
  change Ready09 E9 (workState initial w 9) w at h9
  have hr8 := runBodyFrom_slice E E9 259 26 state hb8
  change program.bb4.runBodyFrom E 259 state = program.bb4.runBodyFrom E9 285 state at hr8
  obtain ⟨E10, hb9, h10, hc10, hf9⟩ := full_step09 E9 state (workState initial w 9) w kp h9 hc9 hw hk
  change Ready10 E10 (workState initial w 10) w at h10
  have hr9 := runBodyFrom_slice E9 E10 285 26 state hb9
  change program.bb4.runBodyFrom E9 285 state = program.bb4.runBodyFrom E10 311 state at hr9
  obtain ⟨E11, hb10, h11, hc11, hf10⟩ := full_step10 E10 state (workState initial w 10) w kp h10 hc10 hw hk
  change Ready11 E11 (workState initial w 11) w at h11
  have hr10 := runBodyFrom_slice E10 E11 311 26 state hb10
  change program.bb4.runBodyFrom E10 311 state = program.bb4.runBodyFrom E11 337 state at hr10
  obtain ⟨E12, hb11, h12, hc12, hf11⟩ := full_step11 E11 state (workState initial w 11) w kp h11 hc11 hw hk
  change Ready12 E12 (workState initial w 12) w at h12
  have hr11 := runBodyFrom_slice E11 E12 337 26 state hb11
  change program.bb4.runBodyFrom E11 337 state = program.bb4.runBodyFrom E12 363 state at hr11
  obtain ⟨E13, hb12, h13, hc13, hf12⟩ := full_step12 E12 state (workState initial w 12) w kp h12 hc12 hw hk
  change Ready13 E13 (workState initial w 13) w at h13
  have hr12 := runBodyFrom_slice E12 E13 363 26 state hb12
  change program.bb4.runBodyFrom E12 363 state = program.bb4.runBodyFrom E13 389 state at hr12
  obtain ⟨E14, hb13, h14, hc14, hf13⟩ := full_step13 E13 state (workState initial w 13) w kp h13 hc13 hw hk
  change Ready14 E14 (workState initial w 14) w at h14
  have hr13 := runBodyFrom_slice E13 E14 389 26 state hb13
  change program.bb4.runBodyFrom E13 389 state = program.bb4.runBodyFrom E14 415 state at hr13
  obtain ⟨E15, hb14, h15, hc15, hf14⟩ := full_step14 E14 state (workState initial w 14) w kp h14 hc14 hw hk
  change Ready15 E15 (workState initial w 15) w at h15
  have hr14 := runBodyFrom_slice E14 E15 415 26 state hb14
  change program.bb4.runBodyFrom E14 415 state = program.bb4.runBodyFrom E15 441 state at hr14
  obtain ⟨E16, hb15, h16, hc16, hf15⟩ := full_step15 E15 state (workState initial w 15) w kp h15 hc15 hw hk
  change Ready16 E16 (workState initial w 16) w at h16
  have hr15 := runBodyFrom_slice E15 E16 441 26 state hb15
  change program.bb4.runBodyFrom E15 441 state = program.bb4.runBodyFrom E16 467 state at hr15
  refine ⟨E16, ?_, h16, hc16, (((((((hf8).trans hf9).trans hf10).trans hf11).trans hf12).trans hf13).trans hf14).trans hf15⟩
  exact (((((((hr8).trans hr9).trans hr10).trans hr11).trans hr12).trans hr13).trans hr14).trans hr15

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull

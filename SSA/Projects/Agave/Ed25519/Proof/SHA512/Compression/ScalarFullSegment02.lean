import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullWorkState
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound16
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound17
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound18
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound19
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound20
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound21
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound22
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound23

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Spec

theorem full_segment02 (E : Env program.Γ) (state : GlobalState)
    (initial : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready16 E (workState initial w 16) w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', program.bb4.runBodyFrom E 467 state =
      program.bb4.runBodyFrom E' 779 state ∧
      Ready24 E' (workState initial w 24) w ∧ Constants E' kp ∧ Frame E E' := by
  obtain ⟨E17, hb16, h17, hc17, hf16⟩ := full_step16 E state (workState initial w 16) w kp h hc hw hk
  change Ready17 E17 (workState initial w 17) w at h17
  have hr16 := runBodyFrom_slice E E17 467 39 state hb16
  change program.bb4.runBodyFrom E 467 state = program.bb4.runBodyFrom E17 506 state at hr16
  obtain ⟨E18, hb17, h18, hc18, hf17⟩ := full_step17 E17 state (workState initial w 17) w kp h17 hc17 hw hk
  change Ready18 E18 (workState initial w 18) w at h18
  have hr17 := runBodyFrom_slice E17 E18 506 39 state hb17
  change program.bb4.runBodyFrom E17 506 state = program.bb4.runBodyFrom E18 545 state at hr17
  obtain ⟨E19, hb18, h19, hc19, hf18⟩ := full_step18 E18 state (workState initial w 18) w kp h18 hc18 hw hk
  change Ready19 E19 (workState initial w 19) w at h19
  have hr18 := runBodyFrom_slice E18 E19 545 39 state hb18
  change program.bb4.runBodyFrom E18 545 state = program.bb4.runBodyFrom E19 584 state at hr18
  obtain ⟨E20, hb19, h20, hc20, hf19⟩ := full_step19 E19 state (workState initial w 19) w kp h19 hc19 hw hk
  change Ready20 E20 (workState initial w 20) w at h20
  have hr19 := runBodyFrom_slice E19 E20 584 39 state hb19
  change program.bb4.runBodyFrom E19 584 state = program.bb4.runBodyFrom E20 623 state at hr19
  obtain ⟨E21, hb20, h21, hc21, hf20⟩ := full_step20 E20 state (workState initial w 20) w kp h20 hc20 hw hk
  change Ready21 E21 (workState initial w 21) w at h21
  have hr20 := runBodyFrom_slice E20 E21 623 39 state hb20
  change program.bb4.runBodyFrom E20 623 state = program.bb4.runBodyFrom E21 662 state at hr20
  obtain ⟨E22, hb21, h22, hc22, hf21⟩ := full_step21 E21 state (workState initial w 21) w kp h21 hc21 hw hk
  change Ready22 E22 (workState initial w 22) w at h22
  have hr21 := runBodyFrom_slice E21 E22 662 39 state hb21
  change program.bb4.runBodyFrom E21 662 state = program.bb4.runBodyFrom E22 701 state at hr21
  obtain ⟨E23, hb22, h23, hc23, hf22⟩ := full_step22 E22 state (workState initial w 22) w kp h22 hc22 hw hk
  change Ready23 E23 (workState initial w 23) w at h23
  have hr22 := runBodyFrom_slice E22 E23 701 39 state hb22
  change program.bb4.runBodyFrom E22 701 state = program.bb4.runBodyFrom E23 740 state at hr22
  obtain ⟨E24, hb23, h24, hc24, hf23⟩ := full_step23 E23 state (workState initial w 23) w kp h23 hc23 hw hk
  change Ready24 E24 (workState initial w 24) w at h24
  have hr23 := runBodyFrom_slice E23 E24 740 39 state hb23
  change program.bb4.runBodyFrom E23 740 state = program.bb4.runBodyFrom E24 779 state at hr23
  refine ⟨E24, ?_, h24, hc24, (((((((hf16).trans hf17).trans hf18).trans hf19).trans hf20).trans hf21).trans hf22).trans hf23⟩
  exact (((((((hr16).trans hr17).trans hr18).trans hr19).trans hr20).trans hr21).trans hr22).trans hr23

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull

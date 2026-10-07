import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullWorkState
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound40
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound41
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound42
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound43
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound44
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound45
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound46
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound47

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Spec

theorem full_segment05 (E : Env program.Γ) (state : GlobalState)
    (initial : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready40 E (workState initial w 40) w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', program.bb4.runBodyFrom E 1403 state =
      program.bb4.runBodyFrom E' 1715 state ∧
      Ready48 E' (workState initial w 48) w ∧ Constants E' kp ∧ Frame E E' := by
  obtain ⟨E41, hb40, h41, hc41, hf40⟩ := full_step40 E state (workState initial w 40) w kp h hc hw hk
  change Ready41 E41 (workState initial w 41) w at h41
  have hr40 := runBodyFrom_slice E E41 1403 39 state hb40
  change program.bb4.runBodyFrom E 1403 state = program.bb4.runBodyFrom E41 1442 state at hr40
  obtain ⟨E42, hb41, h42, hc42, hf41⟩ := full_step41 E41 state (workState initial w 41) w kp h41 hc41 hw hk
  change Ready42 E42 (workState initial w 42) w at h42
  have hr41 := runBodyFrom_slice E41 E42 1442 39 state hb41
  change program.bb4.runBodyFrom E41 1442 state = program.bb4.runBodyFrom E42 1481 state at hr41
  obtain ⟨E43, hb42, h43, hc43, hf42⟩ := full_step42 E42 state (workState initial w 42) w kp h42 hc42 hw hk
  change Ready43 E43 (workState initial w 43) w at h43
  have hr42 := runBodyFrom_slice E42 E43 1481 39 state hb42
  change program.bb4.runBodyFrom E42 1481 state = program.bb4.runBodyFrom E43 1520 state at hr42
  obtain ⟨E44, hb43, h44, hc44, hf43⟩ := full_step43 E43 state (workState initial w 43) w kp h43 hc43 hw hk
  change Ready44 E44 (workState initial w 44) w at h44
  have hr43 := runBodyFrom_slice E43 E44 1520 39 state hb43
  change program.bb4.runBodyFrom E43 1520 state = program.bb4.runBodyFrom E44 1559 state at hr43
  obtain ⟨E45, hb44, h45, hc45, hf44⟩ := full_step44 E44 state (workState initial w 44) w kp h44 hc44 hw hk
  change Ready45 E45 (workState initial w 45) w at h45
  have hr44 := runBodyFrom_slice E44 E45 1559 39 state hb44
  change program.bb4.runBodyFrom E44 1559 state = program.bb4.runBodyFrom E45 1598 state at hr44
  obtain ⟨E46, hb45, h46, hc46, hf45⟩ := full_step45 E45 state (workState initial w 45) w kp h45 hc45 hw hk
  change Ready46 E46 (workState initial w 46) w at h46
  have hr45 := runBodyFrom_slice E45 E46 1598 39 state hb45
  change program.bb4.runBodyFrom E45 1598 state = program.bb4.runBodyFrom E46 1637 state at hr45
  obtain ⟨E47, hb46, h47, hc47, hf46⟩ := full_step46 E46 state (workState initial w 46) w kp h46 hc46 hw hk
  change Ready47 E47 (workState initial w 47) w at h47
  have hr46 := runBodyFrom_slice E46 E47 1637 39 state hb46
  change program.bb4.runBodyFrom E46 1637 state = program.bb4.runBodyFrom E47 1676 state at hr46
  obtain ⟨E48, hb47, h48, hc48, hf47⟩ := full_step47 E47 state (workState initial w 47) w kp h47 hc47 hw hk
  change Ready48 E48 (workState initial w 48) w at h48
  have hr47 := runBodyFrom_slice E47 E48 1676 39 state hb47
  change program.bb4.runBodyFrom E47 1676 state = program.bb4.runBodyFrom E48 1715 state at hr47
  refine ⟨E48, ?_, h48, hc48, (((((((hf40).trans hf41).trans hf42).trans hf43).trans hf44).trans hf45).trans hf46).trans hf47⟩
  exact (((((((hr40).trans hr41).trans hr42).trans hr43).trans hr44).trans hr45).trans hr46).trans hr47

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull

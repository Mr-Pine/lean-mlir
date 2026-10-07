import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullWorkState
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound32
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound33
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound34
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound35
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound36
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound37
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound38
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound39

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Spec

theorem full_segment04 (E : Env program.Γ) (state : GlobalState)
    (initial : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready32 E (workState initial w 32) w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', program.bb4.runBodyFrom E 1091 state =
      program.bb4.runBodyFrom E' 1403 state ∧
      Ready40 E' (workState initial w 40) w ∧ Constants E' kp ∧ Frame E E' := by
  obtain ⟨E33, hb32, h33, hc33, hf32⟩ := full_step32 E state (workState initial w 32) w kp h hc hw hk
  change Ready33 E33 (workState initial w 33) w at h33
  have hr32 := runBodyFrom_slice E E33 1091 39 state hb32
  change program.bb4.runBodyFrom E 1091 state = program.bb4.runBodyFrom E33 1130 state at hr32
  obtain ⟨E34, hb33, h34, hc34, hf33⟩ := full_step33 E33 state (workState initial w 33) w kp h33 hc33 hw hk
  change Ready34 E34 (workState initial w 34) w at h34
  have hr33 := runBodyFrom_slice E33 E34 1130 39 state hb33
  change program.bb4.runBodyFrom E33 1130 state = program.bb4.runBodyFrom E34 1169 state at hr33
  obtain ⟨E35, hb34, h35, hc35, hf34⟩ := full_step34 E34 state (workState initial w 34) w kp h34 hc34 hw hk
  change Ready35 E35 (workState initial w 35) w at h35
  have hr34 := runBodyFrom_slice E34 E35 1169 39 state hb34
  change program.bb4.runBodyFrom E34 1169 state = program.bb4.runBodyFrom E35 1208 state at hr34
  obtain ⟨E36, hb35, h36, hc36, hf35⟩ := full_step35 E35 state (workState initial w 35) w kp h35 hc35 hw hk
  change Ready36 E36 (workState initial w 36) w at h36
  have hr35 := runBodyFrom_slice E35 E36 1208 39 state hb35
  change program.bb4.runBodyFrom E35 1208 state = program.bb4.runBodyFrom E36 1247 state at hr35
  obtain ⟨E37, hb36, h37, hc37, hf36⟩ := full_step36 E36 state (workState initial w 36) w kp h36 hc36 hw hk
  change Ready37 E37 (workState initial w 37) w at h37
  have hr36 := runBodyFrom_slice E36 E37 1247 39 state hb36
  change program.bb4.runBodyFrom E36 1247 state = program.bb4.runBodyFrom E37 1286 state at hr36
  obtain ⟨E38, hb37, h38, hc38, hf37⟩ := full_step37 E37 state (workState initial w 37) w kp h37 hc37 hw hk
  change Ready38 E38 (workState initial w 38) w at h38
  have hr37 := runBodyFrom_slice E37 E38 1286 39 state hb37
  change program.bb4.runBodyFrom E37 1286 state = program.bb4.runBodyFrom E38 1325 state at hr37
  obtain ⟨E39, hb38, h39, hc39, hf38⟩ := full_step38 E38 state (workState initial w 38) w kp h38 hc38 hw hk
  change Ready39 E39 (workState initial w 39) w at h39
  have hr38 := runBodyFrom_slice E38 E39 1325 39 state hb38
  change program.bb4.runBodyFrom E38 1325 state = program.bb4.runBodyFrom E39 1364 state at hr38
  obtain ⟨E40, hb39, h40, hc40, hf39⟩ := full_step39 E39 state (workState initial w 39) w kp h39 hc39 hw hk
  change Ready40 E40 (workState initial w 40) w at h40
  have hr39 := runBodyFrom_slice E39 E40 1364 39 state hb39
  change program.bb4.runBodyFrom E39 1364 state = program.bb4.runBodyFrom E40 1403 state at hr39
  refine ⟨E40, ?_, h40, hc40, (((((((hf32).trans hf33).trans hf34).trans hf35).trans hf36).trans hf37).trans hf38).trans hf39⟩
  exact (((((((hr32).trans hr33).trans hr34).trans hr35).trans hr36).trans hr37).trans hr38).trans hr39

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull

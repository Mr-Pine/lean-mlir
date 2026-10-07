import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound79
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullSegment00
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullSegment01
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullSegment02
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullSegment03
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullSegment04
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullSegment05
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullSegment06
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullSegment07
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullSegment08
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullSegment09

/-! All eighty rounds and fused feed-forward in the original imported bb4. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Spec

theorem scalar_all_rounds (E : Env program.Γ) (state : GlobalState)
    (initial : Spec.State) (w : Nat → Word) (kp : Pointer)
    (hi : InitialReady E initial) (h : Ready00 E initial w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', program.bb4.runBodyFrom E 50 state = program.bb4.runBodyFrom E' 2970 state ∧
      ResultReady E' (feedForward initial (workState initial w 80)) ∧
      Constants E' kp ∧ Frame E E' := by
  obtain ⟨E8, hr0, h8, hc8, hf0⟩ := full_segment00 E state initial w kp h hc hw hk
  obtain ⟨E16, hr1, h16, hc16, hf1⟩ := full_segment01 E8 state initial w kp h8 hc8 hw hk
  obtain ⟨E24, hr2, h24, hc24, hf2⟩ := full_segment02 E16 state initial w kp h16 hc16 hw hk
  obtain ⟨E32, hr3, h32, hc32, hf3⟩ := full_segment03 E24 state initial w kp h24 hc24 hw hk
  obtain ⟨E40, hr4, h40, hc40, hf4⟩ := full_segment04 E32 state initial w kp h32 hc32 hw hk
  obtain ⟨E48, hr5, h48, hc48, hf5⟩ := full_segment05 E40 state initial w kp h40 hc40 hw hk
  obtain ⟨E56, hr6, h56, hc56, hf6⟩ := full_segment06 E48 state initial w kp h48 hc48 hw hk
  obtain ⟨E64, hr7, h64, hc64, hf7⟩ := full_segment07 E56 state initial w kp h56 hc56 hw hk
  obtain ⟨E72, hr8, h72, hc72, hf8⟩ := full_segment08 E64 state initial w kp h64 hc64 hw hk
  obtain ⟨E79, hr9, h79, hc79, hf9⟩ := full_segment09 E72 state initial w kp h72 hc72 hw hk
  have hf79 := (((((((((hf0).trans hf1).trans hf2).trans hf3).trans hf4).trans hf5).trans hf6).trans hf7).trans hf8).trans hf9
  obtain ⟨E80, hb79, h80, hc80, hf80⟩ := full_step79 E79 state initial
    (workState initial w 79) w kp (hi.of_frame hf79) h79 hc79 hw hk
  change ResultReady E80 (feedForward initial (workState initial w 80)) at h80
  have hr79 := runBodyFrom_slice E79 E80 2924 46 state hb79
  change program.bb4.runBodyFrom E79 2924 state = program.bb4.runBodyFrom E80 2970 state at hr79
  refine ⟨E80, ?_, h80, hc80, hf79.trans hf80⟩
  exact ((((((((((hr0).trans hr1).trans hr2).trans hr3).trans hr4).trans hr5).trans hr6).trans hr7).trans hr8).trans hr9).trans hr79

/-- Refinement of the scalar arithmetic body to the independent SHA-512
compression state. Byte decoding, table reads and the final stores are
explicit boundary obligations; no backend compression result is assumed. -/
theorem scalar_rounds_compressBlock (E : Env program.Γ) (state : GlobalState)
    (initial : Spec.State) (block : Agave.Ed25519.Bridge.Challenge.Bytes) (kp : Pointer)
    (hi : InitialReady E initial)
    (h : Ready00 E initial (fun r => (schedule block).getD r 0))
    (hc : Constants E kp) (hk : KRead state.mem kp) :
    ∃ E', program.bb4.runBodyFrom E 50 state = program.bb4.runBodyFrom E' 2970 state ∧
      ResultReady E' (compressBlock initial block) ∧ Constants E' kp ∧ Frame E E' := by
  simpa only [workState_eq_roundsFrom, compressBlock] using
    scalar_all_rounds E state initial (fun r => (schedule block).getD r 0) kp
      hi h hc (schedule_ready block) hk

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull

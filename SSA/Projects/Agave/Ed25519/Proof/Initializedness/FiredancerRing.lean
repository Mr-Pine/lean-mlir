import SSA.Projects.Agave.Ed25519.Proof.Initializedness.Observations
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreEightyRounds

namespace Agave.Ed25519.Initializedness
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
open Agave.Ed25519.Verifier.Execution
namespace FiredancerRing
open Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec

/-- The eighty actual imported round blocks produce the same working state in
two memories with equal message bytes, without any initial ring-value premise.
The first sixteen stores and subsequent ring invariant provide the bridge. -/
theorem rounds_ignore_initial_ring
    (stack data kp : Pointer) (E₁ E₂ : Env program.Γ)
    (before₁ before₂ : GlobalState) (initial : State)
    (h₁ : FirstLoopReady E₁ stack data kp 0 initial)
    (h₂ : FirstLoopReady E₂ stack data kp 0 initial)
    (hs₁ : SmallRange before₁.mem stack 128) (hd₁ : SmallRange before₁.mem data 128)
    (hk₁ : SmallRange before₁.mem kp 640)
    (hs₂ : SmallRange before₂.mem stack 128) (hd₂ : SmallRange before₂.mem data 128)
    (hk₂ : SmallRange before₂.mem kp 640)
    (hne : stack.id ≠ kp.id) (hnd : stack.id ≠ data.id)
    (hread₁ : ∀ j, j < 80 → before₁.mem.readAt (kp.add (BitVec.ofNat 64 (8 * j))) 64 =
      constants.toList.getD j 0)
    (hread₂ : ∀ j, j < 80 → before₂.mem.readAt (kp.add (BitVec.ofNat 64 (8 * j))) 64 =
      constants.toList.getD j 0)
    (hdata : Challenge.readBytes before₁.mem data 128 = Challenge.readBytes before₂.mem data 128) :
    ∃ F₁ after₁ F₂ after₂,
      EightyTrace E₁ before₁ F₁ after₁ ∧ EightyTrace E₂ before₂ F₂ after₂ ∧
      FinalReady F₁ (roundsFrom initial (schedule (Challenge.readBytes before₁.mem data 128)) 0 80) ∧
      FinalReady F₂ (roundsFrom initial (schedule (Challenge.readBytes before₁.mem data 128)) 0 80) ∧
      RingWrites stack before₁ after₁ ∧ RingWrites stack before₂ after₂ := by
  obtain ⟨F₁, after₁, ht₁, hf₁, hw₁, _⟩ :=
    eighty_from_input stack data kp E₁ before₁ initial h₁ hs₁ hd₁ hk₁ hne hnd hread₁
  obtain ⟨F₂, after₂, ht₂, hf₂, hw₂, _⟩ :=
    eighty_from_input stack data kp E₂ before₂ initial h₂ hs₂ hd₂ hk₂ hne hnd hread₂
  rw [← hdata] at hf₂
  exact ⟨F₁, after₁, F₂, after₂, ht₁, ht₂, hf₁, hf₂, hw₁, hw₂⟩

end FiredancerRing

end Agave.Ed25519.Initializedness

import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkTailLoop
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairFrame
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionTrace

/-! Finite execution of bb13 rounds 64..79, including an exact register frame.
The trace ends before the real bb14 executes and preserves GlobalState. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

abbrev BulkTailFrame (before after : Env program.Γ) : Prop := RegFrame 573 609 before after

theorem bulkTailBodyEnv_frame (E : Env program.Γ) (scratch : Pointer) (r : Nat)
    (s : Spec.State) (kw : Word) : BulkTailFrame E (bulkTailBodyEnv E scratch r s kw) := by
  unfold bulkTailBodyEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

theorem bulkTailNextEnv_frame (E : Env program.Γ) (r : Nat) (s : Spec.State) :
    BulkTailFrame E (bulkTailNextEnv E r s) := by
  unfold bulkTailNextEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

theorem bulkTailRoundEnv_frame (E : Env program.Γ) (scratch : Pointer) (r : Nat)
    (s : Spec.State) (kw : Word) :
    BulkTailFrame E
      (bulkTailNextEnv (bulkTailBodyEnv E scratch r s kw) (r + 1) (tailRound s kw)) :=
  (bulkTailBodyEnv_frame E scratch r s kw).trans (bulkTailNextEnv_frame _ _ _)

private theorem roundsFrom_first (s : Spec.State) (words : List Word) (r n : Nat) :
    roundsFrom s words r (n + 1) =
      roundsFrom (Spec.round s (words.getD r 0) (constants.toList.getD r 0))
        words (r + 1) n := by
  have h := roundsFrom_add s words r 1 n
  simpa only [Nat.add_comm 1 n, roundsFrom, Nat.add_zero] using h

/-- Any nonempty suffix of rounds 64..79 executes the prescribed rounds and
lands at bb14. The finite trace preserves the whole global state. -/
theorem bulkTail_suffix (g : Globals) (mem : GlobalState) (scratch : Pointer) (words : List Word)
    (hs : TailSchedule mem.mem scratch words) (n : Nat) :
    ∀ (r : Nat) (_hlo : 64 ≤ r) (_hend : r + n = 79)
      (E : Env program.Γ) (s : Spec.State), BulkTailReady E scratch r s →
      ∃ E', ExecTrace (program g) (n + 1) E 13 mem E' 14 mem ∧
        BulkTailFinalReady E' (roundsFrom s words r (n + 1)) ∧ BulkTailFrame E E' := by
  induction n with
  | zero =>
    intro r hlo hend E s h
    have hr : r = 79 := by omega
    subst r
    refine ⟨bulkTailBodyEnv E scratch 79 s
      (constants.toList.getD 79 0 + words.getD 79 0),
      .single (bulkTail_exit E mem scratch s words h hs), ?_, bulkTailBodyEnv_frame _ _ _ _ _⟩
    have hf := bulkTail_final_ready E scratch 79 s
      (constants.toList.getD 79 0 + words.getD 79 0) h
    rw [tailRound_eq] at hf
    simpa only [roundsFrom, Nat.add_zero] using hf
  | succ n ih =>
    intro r hlo hend E s h
    have hr : r < 79 := by omega
    let kw := constants.toList.getD r 0 + words.getD r 0
    let E₁ := bulkTailNextEnv (bulkTailBodyEnv E scratch r s kw) (r + 1) (tailRound s kw)
    have hready : BulkTailReady E₁ scratch (r + 1) (tailRound s kw) :=
      bulkTail_next_ready E scratch r s kw h
    obtain ⟨E', htrace, hfinal, hframe⟩ :=
      ih (r + 1) (by omega) (by omega) E₁ (tailRound s kw) hready
    refine ⟨E', .step (bulkTail_backedge E mem scratch r s words hlo hr h hs) htrace,
      ?_, (bulkTailRoundEnv_frame E scratch r s kw).trans hframe⟩
    rw [roundsFrom_first]
    simpa only [kw, tailRound_eq] using hfinal

/-- All final sixteen rounds of the exact imported AVX2 implementation.
The only data premise is the concrete K+W scratch contents and live range. -/
theorem bulkTail_sixteen (g : Globals) (mem : GlobalState) (scratch : Pointer) (words : List Word)
    (E : Env program.Γ) (s : Spec.State)
    (hs : TailSchedule mem.mem scratch words) (h : BulkTailReady E scratch 64 s) :
    ∃ E', ExecTrace (program g) 16 E 13 mem E' 14 mem ∧
      BulkTailFinalReady E' (roundsFrom s words 64 16) ∧ BulkTailFrame E E' :=
  bulkTail_suffix g mem scratch words hs 15 64 (by decide) (by decide) E s h

/-- Composition interface for the rest of the imported compression routine. -/
theorem bulkTail_sixteen_runFrom (g : Globals) (mem : GlobalState) (scratch : Pointer)
    (words : List Word) (E : Env program.Γ) (s : Spec.State)
    (hs : TailSchedule mem.mem scratch words) (h : BulkTailReady E scratch 64 s) :
    ∃ E', (program g).runFrom E 13 mem = (program g).runFrom E' 14 mem ∧
      BulkTailFinalReady E' (roundsFrom s words 64 16) ∧ BulkTailFrame E E' := by
  obtain ⟨E', htrace, hfinal, hframe⟩ := bulkTail_sixteen g mem scratch words E s hs h
  exact ⟨E', htrace.runFrom, hfinal, hframe⟩

/-- When the preceding loop has completed round 63, the exact tail supplies
all eighty standard rounds. This is the direct composition interface for the
preceding vector-schedule proof. -/
theorem bulkTail_sixteen_from_prefix (g : Globals) (mem : GlobalState) (scratch : Pointer)
    (words : List Word) (E : Env program.Γ) (initial : Spec.State)
    (hs : TailSchedule mem.mem scratch words)
    (h : BulkTailReady E scratch 64 (roundsFrom initial words 0 64)) :
    ∃ E', ExecTrace (program g) 16 E 13 mem E' 14 mem ∧
      BulkTailFinalReady E' (roundsFrom initial words 0 80) ∧ BulkTailFrame E E' := by
  have hcompose := roundsFrom_add initial words 0 64 16
  simp only [Nat.zero_add] at hcompose
  rw [hcompose]
  exact bulkTail_sixteen g mem scratch words E _ hs h

end Agave.Ed25519.SHA512.Execution.Avx2

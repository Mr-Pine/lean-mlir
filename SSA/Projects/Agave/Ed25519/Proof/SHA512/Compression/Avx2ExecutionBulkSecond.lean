import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkSecondLoop
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionTrace

/-! An exact finite trace of all eighty second-block rounds, preserving the
whole global state and all registers outside bb15's local register interval. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

/-- In particular, the first-block feed-forward state %610..617 and the outer
loop's counters %358..359 survive all eighty rounds unchanged. -/
def BulkSecondFrame (before after : Env program.Γ) : Prop :=
  after.args = before.args ∧
    ∀ i : Fin program.Γ.n, (i.val < 618 ∨ 653 < i.val) →
      after.vals i = before.vals i

theorem BulkSecondFrame.refl (E : Env program.Γ) : BulkSecondFrame E E :=
  ⟨rfl, fun _ _ => rfl⟩

theorem BulkSecondFrame.trans {E₀ E₁ E₂ : Env program.Γ}
    (h₀ : BulkSecondFrame E₀ E₁) (h₁ : BulkSecondFrame E₁ E₂) :
    BulkSecondFrame E₀ E₂ :=
  ⟨h₁.1.trans h₀.1, fun i hi => (h₁.2 i hi).trans (h₀.2 i hi)⟩

theorem BulkSecondFrame.write {E₀ E₁ : Env program.Γ} (h : BulkSecondFrame E₀ E₁)
    (dst : Dst program.Γ t) (v : t.denote)
    (hlo : 618 ≤ dst.i.val) (hhi : dst.i.val ≤ 653) :
    BulkSecondFrame E₀ (E₁.write dst v) := by
  refine ⟨h.1, ?_⟩
  intro i hi
  have hne : i ≠ dst.i := by
    intro heq
    have hv := congrArg Fin.val heq
    omega
  simpa only [Env.write, Env.set, dite_eq_right hne] using h.2 i hi

theorem bulkSecondBodyEnv_frame (E : Env program.Γ) (cache : Pointer) (r : Nat)
    (s : Spec.State) (kw : Word) :
    BulkSecondFrame E (bulkSecondBodyEnv E cache r s kw) := by
  unfold bulkSecondBodyEnv
  repeat' (apply BulkSecondFrame.write <;> try decide)
  exact BulkSecondFrame.refl E

theorem bulkSecondNextEnv_frame (E : Env program.Γ) (r : Nat) (s : Spec.State) :
    BulkSecondFrame E (bulkSecondNextEnv E r s) := by
  unfold bulkSecondNextEnv
  repeat' (apply BulkSecondFrame.write <;> try decide)
  exact BulkSecondFrame.refl E

theorem bulkSecondRoundEnv_frame (E : Env program.Γ) (cache : Pointer) (r : Nat)
    (s : Spec.State) (kw : Word) :
    BulkSecondFrame E
      (bulkSecondNextEnv (bulkSecondBodyEnv E cache r s kw) (r + 1) (tailRound s kw)) :=
  (bulkSecondBodyEnv_frame E cache r s kw).trans (bulkSecondNextEnv_frame _ _ _)

private theorem bulkSecond_roundsFrom_first (s : Spec.State) (words : List Word)
    (r n : Nat) :
    roundsFrom s words r (n + 1) =
      roundsFrom (Spec.round s (words.getD r 0) (constants.toList.getD r 0))
        words (r + 1) n := by
  have h := roundsFrom_add s words r 1 n
  simpa only [Nat.add_comm 1 n, roundsFrom, Nat.add_zero] using h

/-- Every nonempty suffix of bb15 reaches bb16 after exactly its round count.
The hypothesis describes only cache bytes and concrete live register values. -/
theorem bulkSecond_suffix (g : Globals) (mem : GlobalState) (cache : Pointer)
    (words : List Word) (hs : BulkSecondSchedule mem.mem cache words) (n : Nat) :
    ∀ (r : Nat) (_hend : r + n = 79) (E : Env program.Γ) (s : Spec.State),
      BulkSecondReady E cache r s →
      ∃ E', ExecTrace (program g) (n + 1) E 15 mem E' 16 mem ∧
        BulkSecondFinalReady E' (roundsFrom s words r (n + 1)) ∧ BulkSecondFrame E E' := by
  induction n with
  | zero =>
    intro r hend E s h
    have hr : r = 79 := by omega
    subst r
    refine ⟨bulkSecondBodyEnv E cache 79 s
      (constants.toList.getD 79 0 + words.getD 79 0),
      ExecTrace.single (bulkSecond_exit E mem cache s words h hs), ?_,
      bulkSecondBodyEnv_frame _ _ _ _ _⟩
    have hf := bulkSecond_final_ready E cache 79 s
      (constants.toList.getD 79 0 + words.getD 79 0) h
    rw [tailRound_eq] at hf
    simpa only [roundsFrom, Nat.add_zero] using hf
  | succ n ih =>
    intro r hend E s h
    have hr : r < 79 := by omega
    let kw := constants.toList.getD r 0 + words.getD r 0
    let E₁ := bulkSecondNextEnv (bulkSecondBodyEnv E cache r s kw)
      (r + 1) (tailRound s kw)
    have hready : BulkSecondReady E₁ cache (r + 1) (tailRound s kw) :=
      bulkSecond_next_ready E cache r s kw h
    obtain ⟨E', htrace, hfinal, hframe⟩ :=
      ih (r + 1) (by omega) E₁ (tailRound s kw) hready
    refine ⟨E', ExecTrace.step (bulkSecond_backedge E mem cache r s words hr h hs)
      htrace, ?_, (bulkSecondRoundEnv_frame E cache r s kw).trans hframe⟩
    rw [bulkSecond_roundsFrom_first]
    simpa only [kw, tailRound_eq] using hfinal

/-- All eighty rounds of the imported second-block loop, with exact memory,
allocation counter, register frame, entry block and successor block. -/
theorem bulkSecond_eighty (g : Globals) (mem : GlobalState) (cache : Pointer)
    (words : List Word) (E : Env program.Γ) (s : Spec.State)
    (hs : BulkSecondSchedule mem.mem cache words) (h : BulkSecondReady E cache 0 s) :
    ∃ E', ExecTrace (program g) 80 E 15 mem E' 16 mem ∧
      BulkSecondFinalReady E' (roundsFrom s words 0 80) ∧ BulkSecondFrame E E' :=
  bulkSecond_suffix g mem cache words hs 79 0 (by decide) E s h

/-- The finite trace supports arbitrary continuations at bb16. -/
theorem bulkSecond_eighty_runFrom (g : Globals) (mem : GlobalState) (cache : Pointer)
    (words : List Word) (E : Env program.Γ) (s : Spec.State)
    (hs : BulkSecondSchedule mem.mem cache words) (h : BulkSecondReady E cache 0 s) :
    ∃ E', (program g).runFrom E 15 mem = (program g).runFrom E' 16 mem ∧
      BulkSecondFinalReady E' (roundsFrom s words 0 80) ∧ BulkSecondFrame E E' := by
  obtain ⟨E', htrace, hfinal, hframe⟩ := bulkSecond_eighty g mem cache words E s hs h
  exact ⟨E', htrace.runFrom, hfinal, hframe⟩

/-- Bounded evaluation consumes exactly eighty blocks before executing bb16. -/
theorem bulkSecond_eighty_evalFrom (g : Globals) (mem : GlobalState) (cache : Pointer)
    (words : List Word) (E : Env program.Γ) (s : Spec.State)
    (hs : BulkSecondSchedule mem.mem cache words) (h : BulkSecondReady E cache 0 s) :
    ∃ E', (∀ fuel, (program g).evalFrom (80 + fuel) E 15 mem =
        (program g).evalFrom fuel E' 16 mem) ∧
      BulkSecondFinalReady E' (roundsFrom s words 0 80) ∧ BulkSecondFrame E E' := by
  obtain ⟨E', htrace, hfinal, hframe⟩ := bulkSecond_eighty g mem cache words E s hs h
  exact ⟨E', fun fuel => htrace.evalFrom fuel, hfinal, hframe⟩

end Agave.Ed25519.SHA512.Execution.Avx2

import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionLoop
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionFrame

/-! The concrete bb6 execution trace reaches bb7 after exactly sixteen
iterations. Both the finite trace and continuation equation are exposed, so
an execution equivalence cannot be obtained merely by equating two diverging
or undefined whole-program results. -/

namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Every edge is the semantics of the imported bb6, with unchanged global
state. The final edge lands on the real bb7; all earlier edges return to bb6. -/
inductive TailTrace (mem : GlobalState) : Nat → Env program.Γ → Env program.Γ → Prop
  | last {E E'}
      (step : program.bb6.run program.blockParams E mem = .value ((E', .inr 7), mem)) :
      TailTrace mem 1 E E'
  | more {n E E₁ E'}
      (step : program.bb6.run program.blockParams E mem = .value ((E₁, .inr 6), mem))
      (rest : TailTrace mem n E₁ E') : TailTrace mem (n + 1) E E'

/-- The finite trace composes with an arbitrary continuation at bb7. -/
theorem TailTrace.runFrom {mem : GlobalState} {n : Nat} {E E' : Env program.Γ}
    (h : TailTrace mem n E E') (g : Globals) :
    (program g).runFrom E 6 mem = (program g).runFrom E' 7 mem := by
  induction h with
  | last step =>
    rw [Func.runFrom_eq]
    change (program.bb6.run program.blockParams _ mem >>= fun x =>
      (program g).continue x.1.1 x.1.2 x.2) = _
    rw [step]
    rfl
  | more step rest ih =>
    rw [Func.runFrom_eq]
    change (program.bb6.run program.blockParams _ mem >>= fun x =>
      (program g).continue x.1.1 x.1.2 x.2) = _
    rw [step]
    exact ih

/-- An additional bounded observation of the same actual execution trace. -/
theorem TailTrace.evalFrom {mem : GlobalState} {n : Nat} {E E' : Env program.Γ}
    (h : TailTrace mem n E E') (g : Globals) (fuel : Nat) :
    (program g).evalFrom (n + fuel) E 6 mem = (program g).evalFrom fuel E' 7 mem := by
  induction h with
  | last step =>
    rw [Nat.add_comm 1 fuel]
    simp only [Func.evalFrom, EffectM.bind_eq]
    change (program.bb6.run program.blockParams _ mem >>= _) = _
    rw [step]
    rfl
  | @more n E E₁ E' step rest ih =>
    rw [show n + 1 + fuel = (n + fuel) + 1 by omega]
    simp only [Func.evalFrom, EffectM.bind_eq]
    change (program.bb6.run program.blockParams E mem >>= _) = _
    rw [step]
    exact ih

private theorem roundsFrom_first (s : Spec.State) (words : List Word) (r n : Nat) :
    roundsFrom s words r (n + 1) =
      roundsFrom (Spec.round s (words.getD r 0) (constants.toList.getD r 0))
        words (r + 1) n := by
  have h := roundsFrom_add s words r 1 n
  simpa only [Nat.add_comm 1 n, roundsFrom, Nat.add_zero] using h

/-- Any nonempty suffix of rounds 64..79 executes the prescribed rounds and
lands at bb7. Scratch is read-only throughout, as recorded by TailTrace. -/
theorem tail_suffix (mem : GlobalState) (scratch : Pointer) (words : List Word)
    (hs : TailSchedule mem.mem scratch words) (n : Nat) :
    ∀ (r : Nat) (_hlo : 64 ≤ r) (_hend : r + n = 79)
      (E : Env program.Γ) (s : Spec.State), TailReady E scratch r s →
      ∃ E', TailTrace mem (n + 1) E E' ∧
        TailFinalReady E' (roundsFrom s words r (n + 1)) ∧ TailFrame E E' := by
  induction n with
  | zero =>
    intro r hlo hend E s h
    have hr : r = 79 := by omega
    subst r
    refine ⟨tailBodyEnv E scratch 79 s
      (constants.toList.getD 79 0 + words.getD 79 0),
      .last (tail_exit E mem scratch s words h hs), ?_, tailBodyEnv_frame _ _ _ _ _⟩
    have hf := tail_final_ready E scratch 79 s
      (constants.toList.getD 79 0 + words.getD 79 0) h
    rw [tailRound_eq] at hf
    simpa only [roundsFrom, Nat.add_zero] using hf
  | succ n ih =>
    intro r hlo hend E s h
    have hr : r < 79 := by omega
    let kw := constants.toList.getD r 0 + words.getD r 0
    let E₁ := tailNextEnv (tailBodyEnv E scratch r s kw) (r + 1) (tailRound s kw)
    have hready : TailReady E₁ scratch (r + 1) (tailRound s kw) :=
      tail_next_ready E scratch r s kw h
    obtain ⟨E', htrace, hfinal, hframe⟩ :=
      ih (r + 1) (by omega) (by omega) E₁ (tailRound s kw) hready
    refine ⟨E', .more (tail_backedge E mem scratch r s words hlo hr h hs) htrace,
      ?_, (tailRoundEnv_frame E scratch r s kw).trans hframe⟩
    rw [roundsFrom_first]
    simpa only [kw, tailRound_eq] using hfinal

/-- All final sixteen rounds of the exact imported AVX2 implementation.
The only data premise is the concrete K+W scratch contents and live range. -/
theorem tail_sixteen (mem : GlobalState) (scratch : Pointer) (words : List Word)
    (E : Env program.Γ) (s : Spec.State)
    (hs : TailSchedule mem.mem scratch words) (h : TailReady E scratch 64 s) :
    ∃ E', TailTrace mem 16 E E' ∧
      TailFinalReady E' (roundsFrom s words 64 16) ∧ TailFrame E E' :=
  tail_suffix mem scratch words hs 15 64 (by decide) (by decide) E s h

/-- Composition interface for the rest of the imported compression routine. -/
theorem tail_sixteen_runFrom (g : Globals) (mem : GlobalState) (scratch : Pointer)
    (words : List Word) (E : Env program.Γ) (s : Spec.State)
    (hs : TailSchedule mem.mem scratch words) (h : TailReady E scratch 64 s) :
    ∃ E', (program g).runFrom E 6 mem = (program g).runFrom E' 7 mem ∧
      TailFinalReady E' (roundsFrom s words 64 16) ∧ TailFrame E E' := by
  obtain ⟨E', htrace, hfinal, hframe⟩ := tail_sixteen mem scratch words E s hs h
  exact ⟨E', htrace.runFrom g, hfinal, hframe⟩

/-- When the preceding loop has completed round 63, the exact tail supplies
all eighty standard rounds. This is the direct composition interface for the
preceding vector-schedule proof. -/
theorem tail_sixteen_from_prefix (mem : GlobalState) (scratch : Pointer)
    (words : List Word) (E : Env program.Γ) (initial : Spec.State)
    (hs : TailSchedule mem.mem scratch words)
    (h : TailReady E scratch 64 (roundsFrom initial words 0 64)) :
    ∃ E', TailTrace mem 16 E E' ∧
      TailFinalReady E' (roundsFrom initial words 0 80) ∧ TailFrame E E' := by
  have hcompose := roundsFrom_add initial words 0 64 16
  simp only [Nat.zero_add] at hcompose
  rw [hcompose]
  exact tail_sixteen mem scratch words E _ hs h

end Agave.Ed25519.SHA512.Execution.Avx2

import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairFirst
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairStore

namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

abbrev BulkPairBodyFrame (before after : Env program.Γ) : Prop := RegFrame 488 572 before after

theorem bulkPairFirstEnv_frame (E : Env program.Γ) (scratch : Pointer) (j : Nat)
    (s : Spec.State) (kw : Spec.Word) :
    RegFrame 516 541 E (bulkPairFirstEnv E scratch j s kw) := by
  unfold bulkPairFirstEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

theorem bulkPairSecondEnv_frame (E : Env program.Γ) (pairptr : Pointer)
    (s : Spec.State) (kw : Spec.Word) :
    RegFrame 542 566 E (bulkPairSecondEnv E pairptr s kw) := by
  unfold bulkPairSecondEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

/-- The working state survives the final scratch store and counter updates. -/
theorem BulkPairSecondFinalReady.of_frame {E E' : Env program.Γ} {s : Spec.State}
    (h : BulkPairSecondFinalReady E s) (hf : RegFrame 567 572 E E') :
    BulkPairSecondFinalReady E' s := by
  constructor
  · exact (hf.read (%565)).trans h.a
  · exact (hf.read (%540)).trans h.b
  · exact (hf.read (%484)).trans h.c
  · exact (hf.read (%485)).trans h.d
  · exact (hf.read (%566)).trans h.e
  · exact (hf.read (%541)).trans h.f
  · exact (hf.read (%481)).trans h.g
  · exact (hf.read (%483)).trans h.h

/-- Schedule generation leaves all first-round inputs intact. -/
theorem BulkPairFirstReady.of_frame {E E' : Env program.Γ} {scratch : Pointer}
    {j : Nat} {s : Spec.State} (h : BulkPairFirstReady E scratch j s)
    (hf : RegFrame 488 515 E E') : BulkPairFirstReady E' scratch j s := by
  constructor
  · exact (hf.read (%83)).trans h.scratchPtr
  · exact (hf.read (%471)).trans h.slot
  · exact (hf.read (%484)).trans h.a
  · exact (hf.read (%485)).trans h.b
  · exact (hf.read (%486)).trans h.c
  · exact (hf.read (%487)).trans h.d
  · exact (hf.read (%481)).trans h.e
  · exact (hf.read (%483)).trans h.f
  · exact (hf.read (%482)).trans h.g
  · exact (hf.read (%480)).trans h.h
  · exact (hf.read (%3)).trans h.eight
  · exact (hf.read (%35)).trans h.shift
  · exact (hf.read (%36)).trans h.rot14
  · exact (hf.read (%37)).trans h.rot18
  · exact (hf.read (%38)).trans h.rot41
  · exact (hf.read (%39)).trans h.rot28
  · exact (hf.read (%40)).trans h.rot34
  · exact (hf.read (%41)).trans h.rot39


end Agave.Ed25519.SHA512.Execution.Avx2

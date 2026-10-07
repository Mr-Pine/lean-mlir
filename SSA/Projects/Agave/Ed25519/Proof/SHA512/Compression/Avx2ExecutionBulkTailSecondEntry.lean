import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkTailFeedForward
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkSecondBody

/-! Composition into the second block's concrete bb15 header invariant. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

/-- The fixed bb15 inputs inherited from the imported function entry. -/
structure BulkTailSecondConstants (E : Env program.Γ) (cache : Pointer) : Prop where
  cache : E.read (%82) = .value cache
  eight : E.read (%3) = .value 8#64
  limit : E.read (%79) = .value 640#64
  rot14 : E.read (%36) = .value 50#64
  rot18 : E.read (%37) = .value 46#64
  rot41 : E.read (%38) = .value 23#64
  rot28 : E.read (%39) = .value 36#64
  rot34 : E.read (%40) = .value 30#64
  rot39 : E.read (%41) = .value 25#64

theorem BulkTailSecondConstants.of_frame {E E' : Env program.Γ} {cache : Pointer}
    (h : BulkTailSecondConstants E cache) (hf : BulkTailFrame E E') :
    BulkTailSecondConstants E' cache := by
  constructor
  · exact (hf.read (%82)).trans h.cache
  · exact (hf.read (%3)).trans h.eight
  · exact (hf.read (%79)).trans h.limit
  · exact (hf.read (%36)).trans h.rot14
  · exact (hf.read (%37)).trans h.rot18
  · exact (hf.read (%38)).trans h.rot41
  · exact (hf.read (%39)).trans h.rot28
  · exact (hf.read (%40)).trans h.rot34
  · exact (hf.read (%41)).trans h.rot39

/-- All bb15 working words and its byte counter are initialized by bb14;
its fixed inputs survive the feed-forward writes. -/
theorem bulkTailFeedForward_second_ready (E : Env program.Γ) (cache : Pointer)
    (initial final : Spec.State) (h : BulkTailSecondConstants E cache) :
    BulkSecondReady (bulkTailFeedForwardNextEnv E initial final) cache 0
      (Spec.feedForward initial final) := by
  constructor <;>
    simp [bulkTailFeedForwardNextEnv, bulkTailFeedForwardEnv, mlir_env,
      h.cache, h.eight, h.limit, h.rot14, h.rot18, h.rot41, h.rot28, h.rot34, h.rot39]

/-- Concrete first-block compression completes in 17 blocks, reaching the
second block's ready state and retaining its chaining state for bb16.
No second-block schedule premise is needed until bb15 starts executing. -/
theorem bulkTail_feedForward_second (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (scratch cache : Pointer) (initial : Spec.State)
    (block : Agave.Ed25519.Bridge.Challenge.Bytes)
    (hs : TailSchedule mem.mem scratch (schedule block))
    (ht : BulkTailReady E scratch 64 (roundsFrom initial (schedule block) 0 64))
    (hf : BulkTailFeedForwardReady E initial)
    (hc : BulkTailSecondConstants E cache) :
    ∃ E', ExecTrace (program g) 17 E 13 mem E' 15 mem ∧
      BulkSecondReady E' cache 0 (compressBlock initial block) ∧
      BulkTailFeedForwardFinalReady E' (compressBlock initial block) ∧
      RegFrame 573 626 E E' := by
  obtain ⟨E₁, htrace, hfinal, hframe⟩ :=
    bulkTail_sixteen_from_prefix g mem scratch (schedule block) E initial hs ht
  refine ⟨bulkTailFeedForwardNextEnv E₁ initial (roundsFrom initial (schedule block) 0 80),
    htrace.trans (ExecTrace.single
      (bulkTailFeedForward_block E₁ mem initial _ (hf.of_frame hframe) hfinal)),
    bulkTailFeedForward_second_ready E₁ cache initial _ (hc.of_frame hframe),
    bulkTailFeedForward_final_ready E₁ initial _, ?_⟩
  exact (hframe.enlarge (by decide) (by decide)).trans
    ((bulkTailFeedForwardNextEnv_frame E₁ initial _).enlarge (by decide) (by decide))

end Agave.Ed25519.SHA512.Execution.Avx2

import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkTailSecondEntry
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkSecond
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkControl

/-! Composition of the two sequential chaining-state computations within one pair. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Reduce64.Execution
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

structure BulkCounterReady (E : Env program.Γ) (index pairs : BitVec 64) : Prop where
  index : E.read (%358) = .value index
  pairs : E.read (%359) = .value pairs
  two : E.read (%42) = .value 2#64
  minusOne : E.read (%80) = .value 18446744073709551615#64
  zero : E.read (%2) = .value 0#64

theorem BulkCounterReady.of_frame {E E' : Env program.Γ} {index pairs : BitVec 64}
    (h : BulkCounterReady E index pairs) (hf : RegFrame 360 664 E E') :
    BulkCounterReady E' index pairs := by
  constructor
  · exact (hf.read (%358)).trans h.index
  · exact (hf.read (%359)).trans h.pairs
  · exact (hf.read (%42)).trans h.two
  · exact (hf.read (%80)).trans h.minusOne
  · exact (hf.read (%2)).trans h.zero

theorem BulkChainPointers.of_bulk_frame {E E' : Env program.Γ} {chain : Pointer}
    (h : BulkChainPointers E chain) (hf : RegFrame 350 664 E E') :
    BulkChainPointers E' chain := by
  constructor
  · exact (hf.read (%arg0)).trans h.ptr
  · exact (hf.read (%335)).trans h.p1
  · exact (hf.read (%336)).trans h.p2
  · exact (hf.read (%337)).trans h.p3
  · exact (hf.read (%338)).trans h.p4
  · exact (hf.read (%339)).trans h.p5
  · exact (hf.read (%340)).trans h.p6
  · exact (hf.read (%341)).trans h.p7

theorem BulkTailFeedForwardFinalReady.of_second_frame {E E' : Env program.Γ}
    {s : Spec.State} (h : BulkTailFeedForwardFinalReady E s) (hf : BulkSecondFrame E E') :
    BulkTailFeedForwardFinalReady E' s := by
  have hf' : RegFrame 618 653 E E' := hf
  constructor
  · exact (hf'.read (%610)).trans h.a
  · exact (hf'.read (%611)).trans h.b
  · exact (hf'.read (%612)).trans h.c
  · exact (hf'.read (%613)).trans h.d
  · exact (hf'.read (%614)).trans h.e
  · exact (hf'.read (%615)).trans h.f
  · exact (hf'.read (%616)).trans h.g
  · exact (hf'.read (%617)).trans h.h

theorem bulk_advance_ready_of_rounds {E : Env program.Γ} {first final : Spec.State}
    {index pairs : BitVec 64} (h1 : BulkTailFeedForwardFinalReady E first)
    (h2 : BulkSecondFinalReady E final) (hc : BulkCounterReady E index pairs) :
    BulkAdvanceReady E first final index pairs :=
  ⟨h1.a, h1.b, h1.c, h1.d, h1.e, h1.f, h1.g, h1.h,
    h2.a, h2.b, h2.c, h2.d, h2.e, h2.f, h2.g, h2.h,
    hc.index, hc.pairs, hc.two, hc.minusOne, hc.zero⟩

/-- The scalar completion suffix takes 97 actual blocks, with no memory
writes: first-block tail/feed-forward, then all eighty second-block rounds. -/
theorem bulk_finish_rounds (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (scratch cache : Pointer) (initial : Spec.State) (first second : Bytes)
    (index pairs : BitVec 64)
    (hs : TailSchedule mem.mem scratch (schedule first))
    (hcache : BulkSecondSchedule mem.mem cache (schedule second))
    (ht : BulkTailReady E scratch 64 (roundsFrom initial (schedule first) 0 64))
    (hf : BulkTailFeedForwardReady E initial) (hconst : BulkTailSecondConstants E cache)
    (hcounter : BulkCounterReady E index pairs) :
    ∃ E', ExecTrace (program g) 97 E 13 mem E' 16 mem ∧
      BulkAdvanceReady E' (compressBlock initial first)
        (roundsFrom (compressBlock initial first) (schedule second) 0 80) index pairs ∧
      RegFrame 573 653 E E' := by
  obtain ⟨E1, ht1, hs1, hf1, hframe1⟩ :=
    bulkTail_feedForward_second g E mem scratch cache initial first hs ht hf hconst
  obtain ⟨E2, ht2, hf2, hframe2⟩ :=
    bulkSecond_eighty g mem cache (schedule second) E1 (compressBlock initial first) hcache hs1
  have hframe2' : RegFrame 618 653 E1 E2 := hframe2
  have hframe : RegFrame 573 653 E E2 :=
    (hframe1.enlarge (by decide) (by decide)).trans
      (hframe2'.enlarge (by decide) (by decide))
  exact ⟨E2, ht1.trans ht2,
    bulk_advance_ready_of_rounds (hf1.of_second_frame hframe2) hf2
      (hcounter.of_frame (hframe.enlarge (by decide) (by decide))), hframe⟩

/-- A nonfinal pair feeds both blocks sequentially, advances two input blocks,
and returns to the original two-block header with exactly the same memory. -/
theorem bulk_finish_backedge (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (scratch cache : Pointer) (initial : Spec.State) (first second : Bytes)
    (index pairs : BitVec 64)
    (hs : TailSchedule mem.mem scratch (schedule first))
    (hcache : BulkSecondSchedule mem.mem cache (schedule second))
    (ht : BulkTailReady E scratch 64 (roundsFrom initial (schedule first) 0 64))
    (hf : BulkTailFeedForwardReady E initial) (hconst : BulkTailSecondConstants E cache)
    (hcounter : BulkCounterReady E index pairs)
    (hmore : pairs + 18446744073709551615#64 ≠ 0#64) :
    ∃ E', ExecTrace (program g) 98 E 13 mem E' 9 mem ∧
      BulkOuterReady E' (compressBlock (compressBlock initial first) second)
        (index + 2#64) (pairs + 18446744073709551615#64) ∧
      RegFrame 350 664 E E' := by
  obtain ⟨E1, htrace, hready, hframe⟩ :=
    bulk_finish_rounds g E mem scratch cache initial first second index pairs
      hs hcache ht hf hconst hcounter
  let result := compressBlock (compressBlock initial first) second
  let E2 := bulkAdvanceEnv E1 result index pairs
  refine ⟨bulkNextEnv E2, htrace.trans (ExecTrace.single
      (bulk_advance_backedge E1 mem _ _ index pairs hready hmore)),
    bulk_advance_ready E1 result index pairs, ?_⟩
  exact ((hframe.enlarge (by decide) (by decide)).trans
    ((bulkAdvanceEnv_frame E1 result index pairs).enlarge (by decide) (by decide))).trans
      ((bulkNextEnv_frame E2).enlarge (by decide) (by decide))

/-- The final pair reaches the emitted chain stores with the twice-compressed state. -/
theorem bulk_finish_exit (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (scratch cache chain : Pointer) (initial : Spec.State) (first second : Bytes)
    (index : BitVec 64)
    (hs : TailSchedule mem.mem scratch (schedule first))
    (hcache : BulkSecondSchedule mem.mem cache (schedule second))
    (ht : BulkTailReady E scratch 64 (roundsFrom initial (schedule first) 0 64))
    (hf : BulkTailFeedForwardReady E initial) (hconst : BulkTailSecondConstants E cache)
    (hcounter : BulkCounterReady E index 1#64) (hp : BulkChainPointers E chain) :
    ∃ E', ExecTrace (program g) 98 E 13 mem E' 17 mem ∧
      BulkStoreReady E' chain (compressBlock (compressBlock initial first) second) := by
  obtain ⟨E1, htrace, hready, hframe⟩ :=
    bulk_finish_rounds g E mem scratch cache initial first second index 1#64
      hs hcache ht hf hconst hcounter
  let result := compressBlock (compressBlock initial first) second
  refine ⟨bulkAdvanceEnv E1 result index 1#64,
    htrace.trans (ExecTrace.single (bulk_advance_exit E1 mem _ _ index hready)), ?_⟩
  exact bulk_advance_store_ready E1 chain result index 1#64
    (hp.of_bulk_frame (hframe.enlarge (by decide) (by decide)))

end Agave.Ed25519.SHA512.Execution.Avx2

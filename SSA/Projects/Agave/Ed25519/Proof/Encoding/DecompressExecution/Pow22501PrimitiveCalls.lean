import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Pow22501CallSteps

/-! Construct every primitive-call fact in the exact addition-chain body from
 the checked imported pow2k and multiplication implementations. Intermediate
 memory states and limb expressions remain abstract behind their proved readback
 and per-step word equations. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Pow22501
open LeanMLIR.RIR
open SerialFieldMul
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem initial_callState (s : GlobalState) (r : Pointer) (values : Nat → Words) :
    callState s r values 0 = scratchState s 20 := rfl

attribute [local irreducible] callState wordAt machine Pow2k.iterateSquare

/-- All twenty-one actual helper invocations in the source call order, with
 the local range and disjointness facts needed by the final memcpy. -/
theorem linked_body_calls (s : GlobalState) (r a : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 80) (ha : SmallRange s.mem a 40) :
    BodyCalls pow22501Primitives s r a
      (traceStates s r (wordAt (readLimbs s a))) := by
  let values := wordAt (readLimbs s a)
  change BodyCalls pow22501Primitives s r a (traceStates s r values)
  have hr40 : SmallRange s.mem r 40 := by
    simpa only [Pointer.add_zero] using
      (SerialPoint.Execution.smallRange_add hr (k := 0) (count := 40) (by decide))
  have ha20 := scratchState_live hwf ha 20
  have hread (i k : Nat) (hi : i < k) (hk : k ≤ 21) :
      readLimbs (callState s r values k) (destination s r i) = values i :=
    callState_read_written s r values hwf hr40 hi hk
  have hc0 := callState_pow2k_call s r values hwf hr40 0 1
    (by decide) (by decide) a ha20 (by
      rw [callState_read_old s r values hwf ha (n := 0) (by decide)]
      exact wordAt0 (readLimbs s a))
  have hc1 := callState_pow2k_call s r values hwf hr40 1 1
    (by decide) (by decide) (destination s r 0) (destination_live hwf hr40 0) (by
      rw [hread 0 1 (by decide) (by decide)]
      exact wordAt1 (readLimbs s a))
  have hc2 := callState_pow2k_call s r values hwf hr40 2 1
    (by decide) (by decide) (destination s r 1) (destination_live hwf hr40 1) (by
      rw [hread 1 2 (by decide) (by decide)]
      exact wordAt2 (readLimbs s a))
  have hc3 := callState_mul_call s r values hwf hr40 3
    a (destination s r 2) ha20
    (destination_live hwf hr40 2) (by
      rw [callState_read_old s r values hwf ha (n := 3) (by decide), hread 2 3 (by decide) (by decide)]
      exact wordAt3 (readLimbs s a))
  have hc4 := callState_mul_call s r values hwf hr40 4
    (destination s r 0) (destination s r 3) (destination_live hwf hr40 0)
    (destination_live hwf hr40 3) (by
      rw [hread 0 4 (by decide) (by decide), hread 3 4 (by decide) (by decide)]
      exact wordAt4 (readLimbs s a))
  have hc5 := callState_pow2k_call s r values hwf hr40 5 1
    (by decide) (by decide) (destination s r 4) (destination_live hwf hr40 4) (by
      rw [hread 4 5 (by decide) (by decide)]
      exact wordAt5 (readLimbs s a))
  have hc6 := callState_mul_call s r values hwf hr40 6
    (destination s r 3) (destination s r 5) (destination_live hwf hr40 3)
    (destination_live hwf hr40 5) (by
      rw [hread 3 6 (by decide) (by decide), hread 5 6 (by decide) (by decide)]
      exact wordAt6 (readLimbs s a))
  have hc7 := callState_pow2k_call s r values hwf hr40 7 5
    (by decide) (by decide) (destination s r 6) (destination_live hwf hr40 6) (by
      rw [hread 6 7 (by decide) (by decide)]
      exact wordAt7 (readLimbs s a))
  have hc8 := callState_mul_call s r values hwf hr40 8
    (destination s r 7) (destination s r 6) (destination_live hwf hr40 7)
    (destination_live hwf hr40 6) (by
      rw [hread 7 8 (by decide) (by decide), hread 6 8 (by decide) (by decide)]
      exact wordAt8 (readLimbs s a))
  have hc9 := callState_pow2k_call s r values hwf hr40 9 10
    (by decide) (by decide) (destination s r 8) (destination_live hwf hr40 8) (by
      rw [hread 8 9 (by decide) (by decide)]
      exact wordAt9 (readLimbs s a))
  have hc10 := callState_mul_call s r values hwf hr40 10
    (destination s r 9) (destination s r 8) (destination_live hwf hr40 9)
    (destination_live hwf hr40 8) (by
      rw [hread 9 10 (by decide) (by decide), hread 8 10 (by decide) (by decide)]
      exact wordAt10 (readLimbs s a))
  have hc11 := callState_pow2k_call s r values hwf hr40 11 20
    (by decide) (by decide) (destination s r 10) (destination_live hwf hr40 10) (by
      rw [hread 10 11 (by decide) (by decide)]
      exact wordAt11 (readLimbs s a))
  have hc12 := callState_mul_call s r values hwf hr40 12
    (destination s r 11) (destination s r 10) (destination_live hwf hr40 11)
    (destination_live hwf hr40 10) (by
      rw [hread 11 12 (by decide) (by decide), hread 10 12 (by decide) (by decide)]
      exact wordAt12 (readLimbs s a))
  have hc13 := callState_pow2k_call s r values hwf hr40 13 10
    (by decide) (by decide) (destination s r 12) (destination_live hwf hr40 12) (by
      rw [hread 12 13 (by decide) (by decide)]
      exact wordAt13 (readLimbs s a))
  have hc14 := callState_mul_call s r values hwf hr40 14
    (destination s r 13) (destination s r 8) (destination_live hwf hr40 13)
    (destination_live hwf hr40 8) (by
      rw [hread 13 14 (by decide) (by decide), hread 8 14 (by decide) (by decide)]
      exact wordAt14 (readLimbs s a))
  have hc15 := callState_pow2k_call s r values hwf hr40 15 50
    (by decide) (by decide) (destination s r 14) (destination_live hwf hr40 14) (by
      rw [hread 14 15 (by decide) (by decide)]
      exact wordAt15 (readLimbs s a))
  have hc16 := callState_mul_call s r values hwf hr40 16
    (destination s r 15) (destination s r 14) (destination_live hwf hr40 15)
    (destination_live hwf hr40 14) (by
      rw [hread 15 16 (by decide) (by decide), hread 14 16 (by decide) (by decide)]
      exact wordAt16 (readLimbs s a))
  have hc17 := callState_pow2k_call s r values hwf hr40 17 100
    (by decide) (by decide) (destination s r 16) (destination_live hwf hr40 16) (by
      rw [hread 16 17 (by decide) (by decide)]
      exact wordAt17 (readLimbs s a))
  have hc18 := callState_mul_call s r values hwf hr40 18
    (destination s r 17) (destination s r 16) (destination_live hwf hr40 17)
    (destination_live hwf hr40 16) (by
      rw [hread 17 18 (by decide) (by decide), hread 16 18 (by decide) (by decide)]
      exact wordAt18 (readLimbs s a))
  have hc19 := callState_pow2k_call s r values hwf hr40 19 50
    (by decide) (by decide) (destination s r 18) (destination_live hwf hr40 18) (by
      rw [hread 18 19 (by decide) (by decide)]
      exact wordAt19 (readLimbs s a))
  have hc20 := callState_mul_call s r values hwf hr40 20
    (destination s r 19) (destination s r 14) (destination_live hwf hr40 19)
    (destination_live hwf hr40 14) (by
      rw [hread 19 20 (by decide) (by decide), hread 14 20 (by decide) (by decide)]
      exact wordAt20 (readLimbs s a))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [traceStates, destination, scratchIndex, initial_callState] using hc0
  · simpa [traceStates, destination, scratchIndex, initial_callState] using hc1
  · simpa [traceStates, destination, scratchIndex, initial_callState] using hc2
  · simpa [traceStates, destination, scratchIndex, initial_callState] using hc3
  · simpa [traceStates, destination, scratchIndex, initial_callState] using hc4
  · simpa [traceStates, destination, scratchIndex, initial_callState] using hc5
  · simpa [traceStates, destination, scratchIndex, initial_callState] using hc6
  · simpa [traceStates, destination, scratchIndex, initial_callState] using hc7
  · simpa [traceStates, destination, scratchIndex, initial_callState] using hc8
  · simpa [traceStates, destination, scratchIndex, initial_callState] using hc9
  · simpa [traceStates, destination, scratchIndex, initial_callState] using hc10
  · simpa [traceStates, destination, scratchIndex, initial_callState] using hc11
  · simpa [traceStates, destination, scratchIndex, initial_callState] using hc12
  · simpa [traceStates, destination, scratchIndex, initial_callState] using hc13
  · simpa [traceStates, destination, scratchIndex, initial_callState] using hc14
  · simpa [traceStates, destination, scratchIndex, initial_callState] using hc15
  · simpa [traceStates, destination, scratchIndex, initial_callState] using hc16
  · simpa [traceStates, destination, scratchIndex, initial_callState] using hc17
  · simpa [traceStates, destination, scratchIndex, initial_callState] using hc18
  · simpa [traceStates, destination, scratchIndex, initial_callState] using hc19
  · simpa [traceStates, destination, scratchIndex, initial_callState] using hc20
  · exact callState_live s r values (scratchState_live hwf hr 20) 21
  · exact callState_live s r values (scratch_live hwf (i := 15) (n := 20) (by decide)) 21
  · exact Or.inl (Ne.symm (scratch_ne_old hwf hr.fits 15))

/-- info: 'Agave.Ed25519.Encoding.Decompress.Execution.Pow22501.linked_body_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms linked_body_calls

end Agave.Ed25519.Encoding.Decompress.Execution.Pow22501

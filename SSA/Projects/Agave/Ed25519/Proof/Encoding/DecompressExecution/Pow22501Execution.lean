import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Pow22501PrimitiveCalls

/-! Instantiate the exact addition-chain body with the checked imported
pow2k and multiplication helpers. No helper contract remains a premise. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Pow22501
open LeanMLIR.RIR
open SerialFieldMul
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)

/-- Actual output stores of the imported addition-chain function. -/
def resultState (s : GlobalState) (r : Pointer) (x : Words) : GlobalState :=
  { alloc := ⟨s.alloc.nextFreeBlock + 20⟩,
    mem := (storeLimbs s.mem r (rawWordChain x).1).storeAt
      (r.add 40#64) (limbBytes (rawWordChain x).2) }

private theorem resultState_wordAt (s : GlobalState) (r : Pointer) (x : Words) :
    {alloc := ⟨s.alloc.nextFreeBlock + 20⟩,
     mem := (storeLimbs s.mem r (wordAt x 20)).storeAt (r.add 40#64)
       (limbBytes (wordAt x 4))} = resultState s r x := by
  simp only [wordAt20_eq_first, wordAt4_eq_second, resultState]

/-- Exact execution of the fully linked imported addition-chain helper. -/
theorem program_call (r a : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 80) (ha : SmallRange s.mem a 40) :
    (program pow22501Primitives).call (program.args (.value r) (.value a)) s =
      .value (.nil, resultState s r (readLimbs s a)) := by
  let values := wordAt (readLimbs s a)
  have hr40 : SmallRange s.mem r 40 := by
    simpa only [Pointer.add_zero] using smallRange_add hr (k := 0) (count := 40) (by decide)
  have hc := program_call_of_calls pow22501Primitives r a s (traceStates s r values)
    (linked_body_calls s r a hwf hr ha)
  exact hc.trans (congrArg (fun t : GlobalState => PoisonOr.value (Vals.nil, t))
    ((copyState_erase s r values hwf hr40).trans (resultState_wordAt s r (readLimbs s a))))


/-- Bounds and field denotation are consequences of the executed word chain. -/
theorem program_call_field (r a : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 80) (ha : SmallRange s.mem a 40)
    (htight : SerialPoint.Tight (unsigned (readLimbs s a))) :
    (program pow22501Primitives).call (program.args (.value r) (.value a)) s =
        .value (.nil, resultState s r (readLimbs s a)) ∧
      (wordValue (rawWordChain (readLimbs s a)).1,
        wordValue (rawWordChain (readLimbs s a)).2) =
          Decompress.pow22501 (wordValue (readLimbs s a)) ∧
      SerialPoint.Tight (unsigned (rawWordChain (readLimbs s a)).1) ∧
      SerialPoint.Tight (unsigned (rawWordChain (readLimbs s a)).2) := by
  let x : TightWords := ⟨readLimbs s a, htight⟩
  have hx : rawWordChain (readLimbs s a) =
      ((wordChain x).1.limbs, (wordChain x).2.limbs) := rawWordChain_eq x
  refine ⟨program_call r a s hwf hr ha, ?_, ?_⟩
  · rw [hx]
    exact wordChain_value x
  · rw [hx]
    exact wordChain_tight x

end Agave.Ed25519.Encoding.Decompress.Execution.Pow22501

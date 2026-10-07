import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Tail

/-! Full imported compressor execution, parameterized by the five individual
field-call results and one subtle call result. There is no compressor execution
or byte-encoding premise. Memory/range facts are tied to the exact instruction
which needs them. Applying contracts to produce these facts is separate. -/
namespace Agave.Ed25519.Encoding.Compress.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Named states at exactly the five external field calls in instructions
63, 71, 72, 76 and 79. -/
structure FieldStates where
  powed : GlobalState
  squared : GlobalState
  inverted : GlobalState
  affineX : GlobalState
  affineXY : GlobalState

/-- Only primitive invocation facts and local live-object conditions. -/
structure FieldCalls (p : Primitives) (initial : GlobalState) (input : Pointer)
    (states : FieldStates) : Prop where
  inputLive : SmallRange (scratchState initial 6).mem input 160
  pow22501 : p.pow22501 (.cons (.value (scratch initial 1))
    (.cons (.value (input.add 80)) .nil)) (scratchState initial 6) =
      .value (.nil, states.powed)
  pairLive : SmallRange states.powed.mem (scratch initial 1) 80
  firstLive : SmallRange states.powed.mem (scratch initial 3) 40
  secondLive : SmallRange states.powed.mem (scratch initial 2) 40
  copyFirstDisjoint : (Range.of (scratch initial 3) 320).Disjoint
    (Range.of (scratch initial 1) 320)
  copySecondDisjoint : (Range.of (scratch initial 2) 320).Disjoint
    (Range.of ((scratch initial 1).add 40) 320)
  pow2k : p.pow2k (.cons (.value (scratch initial 0))
    (.cons (.value (scratch initial 3)) (.cons (.value 5#32) .nil)))
    (copySecond initial states.powed) = .value (.nil, states.squared)
  invertMul : p.mul (.cons (.value (scratch initial 4))
    (.cons (.value (scratch initial 0)) (.cons (.value (scratch initial 2)) .nil)))
    states.squared = .value (.nil, states.inverted)
  xMul : p.mul (.cons (.value (scratch initial 5))
    (.cons (.value input) (.cons (.value (scratch initial 4)) .nil)))
    states.inverted = .value (.nil, states.affineX)
  inputLiveAfterX : SmallRange states.affineX.mem input 160
  affineLiveAfterX : SmallRange states.affineX.mem (scratch initial 5) 80
  yMul : p.mul (.cons (.value ((scratch initial 5).add 40))
    (.cons (.value (input.add 40)) (.cons (.value (scratch initial 4)) .nil)))
    states.affineX = .value (.nil, states.affineXY)
  affineLive : SmallRange states.affineXY.mem (scratch initial 5) 80

/-- Full actual body from the entry, with every intervening instruction proved
by the three consecutive instruction-list slices. -/
theorem program_run_of_calls (p : Primitives) (out input : Pointer)
    (initial afterBlack : GlobalState) (states : FieldStates)
    (calls : FieldCalls p initial input states)
    (hsafe : NormalizationSafety (affineXWords states.affineXY (scratch initial 5))
      (affineYWords states.affineXY (scratch initial 5)))
    (hout : SmallRange afterBlack.mem out 32)
    (hblack : p.blackBoxByte (.cons (.value
      (inlineParity (affineXWords states.affineXY (scratch initial 5)))) .nil)
      states.affineXY = .value (.cons (.value
        (inlineParity (affineXWords states.affineXY (scratch initial 5)))) .nil, afterBlack)) :
    (program p).run (program.args (.value out) (.value input)) initial =
      .value (.nil, {afterBlack with
        mem := storeBytes afterBlack.mem out
          (encodedBytes (affineXWords states.affineXY (scratch initial 5))
          (affineYWords states.affineXY (scratch initial 5)))}) := by
  rw [Func.run_runFrom_eq]
  change (program p).runFrom
    (Env.init (program.args (.value out) (.value input)).get) 0 initial = _
  rw [finishFrom_zero]
  let E := Env.init ((program.args (.value out) (.value input)).get)
  have hprefix := affine_prefix_run p E input initial states.powed states.squared
    states.inverted states.affineX states.affineXY rfl calls.inputLive calls.pow22501
    calls.pairLive calls.firstLive calls.secondLive calls.copyFirstDisjoint
    calls.copySecondDisjoint calls.pow2k calls.invertMul calls.xMul calls.inputLiveAfterX
    calls.affineLiveAfterX calls.yMul
  rw [finishFrom_of_slice p 0 81 E _ initial states.affineXY hprefix]
  exact affine_tail_run p E initial states.affineXY afterBlack input out
    calls.affineLive rfl hout hsafe hblack

/-- The actual call also performs the normal RIR stack-frame erasure. -/
theorem program_call_of_calls (p : Primitives) (out input : Pointer)
    (initial afterBlack : GlobalState) (states : FieldStates)
    (calls : FieldCalls p initial input states)
    (hsafe : NormalizationSafety (affineXWords states.affineXY (scratch initial 5))
      (affineYWords states.affineXY (scratch initial 5)))
    (hout : SmallRange afterBlack.mem out 32)
    (hblack : p.blackBoxByte (.cons (.value
      (inlineParity (affineXWords states.affineXY (scratch initial 5)))) .nil)
      states.affineXY = .value (.cons (.value
        (inlineParity (affineXWords states.affineXY (scratch initial 5)))) .nil, afterBlack)) :
    (program p).call (program.args (.value out) (.value input)) initial =
      .value (.nil, {afterBlack with
        mem := (storeBytes afterBlack.mem out
          (encodedBytes (affineXWords states.affineXY (scratch initial 5))
          (affineYWords states.affineXY (scratch initial 5)))).eraseFrom
            initial.alloc.nextFreeBlock}) := by
  exact Func.call_of_run (program_run_of_calls p out input initial afterBlack states
    calls hsafe hout hblack)

end Agave.Ed25519.Encoding.Compress.Execution

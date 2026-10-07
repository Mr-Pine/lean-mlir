import SSA.Projects.Agave.Ed25519.Proof.Verifier.KeyExecution

namespace Agave.Ed25519.Verifier.Execution.Key
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

/-- A single external decoder call and its concrete Option memory. No premise
mentions key execution, and success is not restricted to points of prime order. -/
structure DecoderCall (p : Primitives) (initial decoded : GlobalState)
    (out bytes : Pointer) (x t : Words) (valid : Bool) : Prop where
  call : p.decompress (args (optionSlot initial) bytes) (initial.alloca 168) =
    .value (.nil, decoded)
  optionRange : SmallRange decoded.mem (optionSlot initial) 168
  tag : decoded.mem.readAt (optionSlot initial) 64 = if valid then 1 else 0
  outputRange : SmallRange decoded.mem out 200
  success : valid = true → SmallRange decoded.mem bytes 32 ∧
    out.id ≠ (optionSlot initial).id ∧ out.id ≠ bytes.id ∧
    NegationReads decoded (optionSlot initial) x t

def returnedState (initial decoded : GlobalState) (out bytes : Pointer)
    (x t : Words) (valid : Bool) : GlobalState :=
  let final := outputState decoded out (optionSlot initial) bytes x t valid
  { final with mem := final.mem.eraseFrom initial.alloc.nextFreeBlock }

theorem call_of_decoder (p : Primitives) (initial decoded : GlobalState)
    (out bytes : Pointer) (x t : Words) (valid : Bool)
    (h : DecoderCall p initial decoded out bytes x t valid) :
    (program p).call (args out bytes) initial =
      .value (.nil, returnedState initial decoded out bytes x t valid) :=
  Func.call_of_run (run_of_decoder p initial decoded out bytes x t valid
    h.call h.optionRange h.tag h.outputRange h.success)

/-- Discharges the wrapper's formerly opaque key-constructor call obligation
using its exact imported body, including the flipped Option/Result tag ABI. -/
theorem wrapper_keyCall {Point Scalar : Type} (p : Primitives)
    (w : Wrapper.Primitives) (shared : Shared Point Scalar)
    (i : Invocation) (initial decoded : GlobalState) (a : Bytes32) (x t : Words)
    (hlink : w.keyFromBytes = (program p).call)
    (h : DecoderCall p (Wrapper.allocated initial) decoded (Wrapper.keyResultSlot initial)
      i.publicKey x t (shared.decompress a).isSome) :
    Wrapper.KeyCall w shared i initial
      (returnedState (Wrapper.allocated initial) decoded (Wrapper.keyResultSlot initial)
        i.publicKey x t (shared.decompress a).isSome) a := by
  have hcaller : (Wrapper.keyResultSlot initial).id.id <
      (Wrapper.allocated initial).alloc.nextFreeBlock := by
    simp [Wrapper.keyResultSlot, Wrapper.allocated, GlobalState.allocaPtr, GlobalState.alloca]
  constructor
  · rw [hlink]
    exact call_of_decoder p _ _ _ _ _ _ _ h
  · exact Fits.mono (by decide) (erase_range (output_range h.outputRange) hcaller).fits
  · dsimp only [returnedState]
    rw [erase_read _ _ _ _ hcaller, output_tag h.outputRange]
    cases shared.decompress a <;> rfl

/-- Mathematical decoding and the physical decoder contract imply constructor
refinement on all 256-bit strings. In particular there is no subgroup premise. -/
theorem observe_refines {Point : Type} (decode : Bytes32 → Option Point)
    (p : Primitives) (initial decoded : GlobalState) (out bytes : Pointer)
    (a : Bytes32) (x t : Words)
    (h : DecoderCall p initial decoded out bytes x t (decode a).isSome)
    (hcaller : out.id.id < initial.alloc.nextFreeBlock) :
    observe p initial out bytes = some (decode a).isSome :=
  observe_of_decoder p initial decoded out bytes x t (decode a).isSome
    h.call h.optionRange h.tag h.outputRange h.success hcaller

end Agave.Ed25519.Verifier.Execution.Key

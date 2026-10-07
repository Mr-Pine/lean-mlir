import SSA.Projects.Agave.Ed25519.Proof.Verifier.KeyExecutionContracts

/-!
# Linking the exact key constructor into the byte-input wrapper

The constructor call and Result tag are derived from `Key.DecoderCall`. The
remaining execution hypotheses name only the signature and Dalek calls. The
sole additional memory premise says that the decoder preserves enough space
for the wrapper's 192-byte key destination, and is required only on success.
-/
namespace Agave.Ed25519.Verifier.Execution.WrapperKeyLink

open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

/-- The actual state after the constructor returns and erases its local frame. -/
def afterKey (initial decoded : GlobalState) (i : Invocation)
    (x t : Key.Words) (valid : Bool) : GlobalState :=
  Key.returnedState (Wrapper.allocated initial) decoded (Wrapper.keyResultSlot initial)
    i.publicKey x t valid

/-- Constructor writes preserve the bounds of every allocation. No separation
premise is needed for this size-only property. -/
theorem output_fits (h : Fits state.mem ptr width) :
    Fits (Key.outputState state out opt bytes x t valid).mem ptr width := by
  cases valid <;>
    simpa [Key.outputState, Key.rejectedState,
      Key.successState, Key.payloadState, Key.copyYZ, Fits.storeAt_iff] using h

/-- The constructor's frame erasure preserves caller-owned bounds. -/
theorem erase_fits (h : Fits mem ptr width) (hcaller : ptr.id.id < bound) :
    Fits (mem.eraseFrom bound) ptr width := by
  rcases h with ⟨block, hblock, hsize⟩
  exact ⟨block, (Key.erase_get mem ptr.id bound hcaller).trans hblock, hsize⟩

/-- Both wrapper payload-copy bounds follow before the constructor call returns.
The Result range comes from the decoder contract; the destination requires only
its bit bound, with no small-allocation or disjointness assumption. -/
theorem key_memory (hresult : SmallRange decoded.mem (Wrapper.keyResultSlot initial) 200)
    (hdestination : Fits decoded.mem (Wrapper.keySlot initial) 1536) :
    Wrapper.KeyMemory initial (afterKey initial decoded i x t valid) := by
  have hresultCaller : (Wrapper.keyResultSlot initial).id.id <
      (Wrapper.allocated initial).alloc.nextFreeBlock := by
    simp [Wrapper.keyResultSlot, Wrapper.allocated, GlobalState.allocaPtr, GlobalState.alloca]
  have hkeyCaller : (Wrapper.keySlot initial).id.id <
      (Wrapper.allocated initial).alloc.nextFreeBlock := by
    simp [Wrapper.keySlot, Wrapper.allocated, GlobalState.allocaPtr, GlobalState.alloca]
  constructor
  · exact Key.erase_range (Key.output_range hresult) hresultCaller
  · exact erase_fits (output_fits hdestination) hkeyCaller

/-- The two primitive calls that follow a successful key constructor. The key
state is its exact returned state, rather than an unconstrained witness. -/
structure ContinuationCalls (w : Wrapper.Primitives) (i : Invocation)
    (initial decoded afterSignature afterDalek : GlobalState)
    (x t : Key.Words) (valid accepted : Bool) : Prop where
  destinationFits : Fits decoded.mem (Wrapper.keySlot initial) 1536
  signature : w.signatureFromBytes (Wrapper.ptrArgs (Wrapper.signatureSlot initial) i.signature)
    (Wrapper.copiedKey initial (afterKey initial decoded i x t valid)) =
      .value (.nil, afterSignature)
  dalek : w.verifyDalek
    (Wrapper.dalekArgs (Wrapper.keySlot initial) (Wrapper.signatureSlot initial) i.message i.length)
    afterSignature = .value (.cons (.value (resultCode accepted)) .nil, afterDalek)

/-- Primitive-level obligations after replacing the opaque key call by its
exact body. Mathematical validity enters through the physical decoder tag.
There is no wrapper or key-constructor execution premise. -/
def DecoderPrimitiveCalls {Point Scalar Result : Type}
    (p : Key.Primitives) (w : Wrapper.Primitives) (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (i : Invocation) (initial : GlobalState) (a r s : Bytes32) (message : List (BitVec 8)) : Prop :=
  ∃ decoded x t afterSignature afterDalek,
    Key.DecoderCall p (Wrapper.allocated initial) decoded (Wrapper.keyResultSlot initial)
      i.publicKey x t (shared.decompress a).isSome ∧
    ∀ A, shared.decompress a = some A →
      ContinuationCalls w i initial decoded afterSignature afterDalek x t
        (shared.decompress a).isSome
        (prehashed shared doubleBase compress (shared.negate A) r s (challenge r a message))

section
variable {Point Scalar Result : Type}
variable (p : Key.Primitives) (w : Wrapper.Primitives) (shared : Shared Point Scalar)
variable (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
variable (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
variable (hlink : w.keyFromBytes = (Key.program p).call)
include hlink

/-- Discharge the wrapper contracts with the exact constructor call and the
minimal remaining successful-path primitive contracts. -/
theorem primitive_calls_of_decoder (i : Invocation) (initial : GlobalState)
    (a r s : Bytes32) (message : List (BitVec 8))
    (h : DecoderPrimitiveCalls p w shared doubleBase compress challenge i initial a r s message) :
    Wrapper.PrimitiveCalls w shared doubleBase compress challenge i initial a r s message := by
  rcases h with ⟨decoded, x, t, afterSignature, afterDalek, hdecoder, hcontinuation⟩
  refine ⟨afterKey initial decoded i x t (shared.decompress a).isSome,
    afterSignature, afterDalek, Key.wrapper_keyCall p w shared i initial decoded a x t hlink hdecoder, ?_⟩
  intro A hA
  have hc := hcontinuation A hA
  exact ⟨key_memory hdecoder.outputRange hc.destinationFits, hc.signature, hc.dalek⟩

/-- The byte-input wrapper observes mathematical verification, using the
actual key body under its decoder ABI contract. Rejected keys require no
signature/Dalek call or destination-memory premise. -/
theorem observe_of_decoder_calls (i : Invocation) (initial : GlobalState)
    (a r s : Bytes32) (message : List (BitVec 8))
    (h : DecoderPrimitiveCalls p w shared doubleBase compress challenge i initial a r s message) :
    observe w i initial = some (verify shared doubleBase compress a r s (challenge r a message)) :=
  Wrapper.observe_of_primitive_calls w shared doubleBase compress challenge i initial a r s message
    (primitive_calls_of_decoder p w shared doubleBase compress challenge hlink i initial a r s message h)

/-- Pointwise decoder and continuation obligations suffice for the wrapper's
universal execution-refinement contract. -/
theorem refines_of_decoder_calls (environment : Invocation → GlobalState → Prop)
    (hcalls : ∀ i state a r s message,
      Represents i state a r s message → environment i state →
      DecoderPrimitiveCalls p w shared doubleBase compress challenge i state a r s message) :
    RefinesControlFlow w shared doubleBase compress challenge environment := by
  intro i state a r s message hinput henv
  exact observe_of_decoder_calls p w shared doubleBase compress challenge hlink i state a r s message
    (hcalls i state a r s message hinput henv)

end
end Agave.Ed25519.Verifier.Execution.WrapperKeyLink

import SSA.Projects.Agave.Ed25519.Proof.Verifier.LinkedConcretePayload
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ValidPoint

/-! Transport the decoder's valid limb representative through the actual key
constructor and both wrapper copies, using the existing byte-transport proofs.
No equality of a post-copy cached point is assumed. -/
namespace Agave.Ed25519.Verifier.Execution.LinkedValidPayload
open LeanMLIR.RIR

def Inputs (kp : Key.Primitives) (dg : Dalek.Globals) (cg : Challenge.Globals)
    (decode : Bytes32 → Option ValidPoint) (cofactor : ValidPoint → ValidPoint)
    (i : Invocation) (initial : GlobalState) (a r s : Bytes32) (message : List (BitVec 8)) : Prop :=
  i.length = BitVec.ofNat 64 message.length ∧
  ∃ decoded x t,
    Key.DecoderCall kp (Wrapper.allocated initial) decoded (Wrapper.keyResultSlot initial)
      i.publicKey x t (decode a).isSome ∧
    ∀ A, decode a = some A →
      x = A.words.X ∧ t = A.words.T ∧
      decoded.mem.readAt ((Key.optionSlot (Wrapper.allocated initial)).add 48#64) 320 =
        Key.coordinatePayload A.words.Y ∧
      decoded.mem.readAt ((Key.optionSlot (Wrapper.allocated initial)).add 88#64) 320 =
        Key.coordinatePayload A.words.Z ∧
      LinkedConcretePayload.SignatureMemoryExceptPoint dg cg (ValidPoint.layout cofactor)
        i initial decoded x t (decode a).isSome a r s A.negate message

theorem signatureMemory_of_decoder
    (kp : Key.Primitives) (dg : Dalek.Globals) (cg : Challenge.Globals)
    (cofactor : ValidPoint → ValidPoint) (i : Invocation) (initial decoded : GlobalState)
    (A : ValidPoint) (a r s : Bytes32) (message : List (BitVec 8))
    (hd : Key.DecoderCall kp (Wrapper.allocated initial) decoded (Wrapper.keyResultSlot initial)
      i.publicKey A.words.X A.words.T true)
    (hy : decoded.mem.readAt ((Key.optionSlot (Wrapper.allocated initial)).add 48#64) 320 =
      Key.coordinatePayload A.words.Y)
    (hz : decoded.mem.readAt ((Key.optionSlot (Wrapper.allocated initial)).add 88#64) 320 =
      Key.coordinatePayload A.words.Z)
    (hm : LinkedConcretePayload.SignatureMemoryExceptPoint dg cg (ValidPoint.layout cofactor)
      i initial decoded A.words.X A.words.T true a r s A.negate message) :
    LinkedLeaves.SignatureMemory dg cg (ValidPoint.layout cofactor) i initial decoded
      A.words.X A.words.T true a r s A.negate message := by
  have hcaller : (Wrapper.keyResultSlot initial).id.id <
      (Wrapper.allocated initial).alloc.nextFreeBlock := by
    simp [Wrapper.keyResultSlot, Wrapper.allocated, GlobalState.allocaPtr, GlobalState.alloca]
  have hp : (Key.returnedState (Wrapper.allocated initial) decoded
      (Wrapper.keyResultSlot initial) i.publicKey A.words.X A.words.T true).mem.readAt
      ((Wrapper.keyResultSlot initial).add 40#64) 1280 =
      (ValidPoint.layout cofactor).point A.negate := by
    rw [Key.returned_point_readback _ _ _ _ _ _ hd.outputRange hcaller, hy, hz]
    rfl
  have hread := LinkedConcretePayload.afterSignature_point i initial decoded A.words.X A.words.T _
    (WrapperKeyLink.key_memory hd.outputRange hm.destinationFits) hp
  have hrange := Dalek.smallRange_add hm.memory.keyRange (k := 32) (count := 160) (by decide)
  exact ⟨hm.destinationFits, hm.wellFormed, hm.signatureDestination, hm.signatureSource,
    hm.signatureDisjoint, hm.memory.complete ⟨hrange, hread⟩⟩

/-- Converts raw successful decoder coordinates into the exact-signature
entry package. All point values in that package carry their own invariants. -/
theorem exactSignatureInputs_of_decoder
    (kp : Key.Primitives) (dg : Dalek.Globals) (cg : Challenge.Globals)
    (decode : Bytes32 → Option ValidPoint) (cofactor : ValidPoint → ValidPoint)
    (i : Invocation) (initial : GlobalState) (a r s : Bytes32) (message : List (BitVec 8))
    (h : Inputs kp dg cg decode cofactor i initial a r s message) :
    LinkedLeaves.ExactSignatureInputs kp dg cg (ValidPoint.layout cofactor)
      (ValidPoint.shared decode) i initial a r s message := by
  obtain ⟨hlen, decoded, x, t, hd, hm⟩ := h
  refine ⟨hlen, decoded, x, t, hd, ?_⟩
  intro A hA
  change decode a = some A at hA
  obtain ⟨hx, ht, hy, hz, hmem⟩ := hm A hA
  subst x t
  have hd' : Key.DecoderCall kp (Wrapper.allocated initial) decoded (Wrapper.keyResultSlot initial)
      i.publicKey A.words.X A.words.T true := by simpa [hA] using hd
  have hmem' : LinkedConcretePayload.SignatureMemoryExceptPoint dg cg (ValidPoint.layout cofactor)
      i initial decoded A.words.X A.words.T true a r s A.negate message := by
    simpa [hA] using hmem
  simpa [ValidPoint.shared, hA] using
    signatureMemory_of_decoder kp dg cg cofactor i initial decoded A a r s message hd' hy hz hmem'

end Agave.Ed25519.Verifier.Execution.LinkedValidPayload

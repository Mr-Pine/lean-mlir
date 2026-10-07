import SSA.Projects.Agave.Ed25519.Proof.Verifier.LinkedLeafExecution
import SSA.Projects.Agave.Ed25519.Proof.Verifier.KeyPayloadLayout

/-!
# Concrete cached-point transport into exact Agave execution

The decoder's raw X/T words and Y/Z reads determine the constructor payload.
The wrapper key copy and signature copy transport that payload to Dalek's
cached-minus-A field. This field is a conclusion, not a post-copy layout
assumption. The other entry ranges, byte observations and globals stay explicit.
-/
namespace Agave.Ed25519.Verifier.Execution.LinkedConcretePayload
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

structure EntryMemoryExceptPoint (g : Dalek.Globals) (cg : Challenge.Globals)
    (layout : Dalek.Layout Point Scalar Result) (initial : GlobalState)
    (key signature message : Pointer) (a r bytes : Bytes32) (minusA : Point)
    (msg : List (BitVec 8)) : Prop where
  wellFormed : initial.WF
  keyRange : SmallRange initial.mem key 192
  signatureRange : SmallRange initial.mem signature 64
  messageRange : SmallRange initial.mem message msg.length
  publicKey : initial.mem.readAt key 256 = a
  signatureR : initial.mem.readAt signature 256 = r
  signatureS : initial.mem.readAt (signature.add 32#64) 256 = bytes
  messageBytes : ∀ (i : Nat) (hi : i < msg.length),
    initial.mem.readAt (message.add (BitVec.ofNat 64 i)) 8 = msg[i]
  lengthBound : msg.length < 2 ^ 63
  identity : Dalek.ReadBytes initial g.address0 40 (1#320)
  cache : SmallRange initial.mem g.address1 1
  keyCache : (Range.of (key.add 32#64) 1280).Disjoint (Range.of g.address1 8)
  signatureCache : (Range.of signature 256).Disjoint (Range.of g.address1 8)
  shaIV : Dalek.ReadBytes initial cg.address0 64 Challenge.initialWords


theorem EntryMemoryExceptPoint.complete
    (h : EntryMemoryExceptPoint dg cg layout state key signature message a r s minusA msg)
    (hp : Dalek.ReadBytes state (key.add 32#64) 160 (layout.point minusA)) :
    Dalek.EntryMemory dg cg layout state key signature message a r s minusA msg :=
  ⟨h.wellFormed, h.keyRange, h.signatureRange, h.messageRange, h.publicKey,
    h.signatureR, h.signatureS, hp, h.messageBytes, h.lengthBound, h.identity,
    h.cache, h.keyCache, h.signatureCache, h.shaIV⟩

/-- The wrapper's 192-byte move transports the 160-byte cached point from
Result payload offset 40 to key offset 32. -/
theorem copiedKey_point (initial afterKey : GlobalState) (value : BitVec 1280)
    (hm : Wrapper.KeyMemory initial afterKey)
    (hp : afterKey.mem.readAt ((Wrapper.keyResultSlot initial).add 40#64) 1280 = value) :
    (Wrapper.copiedKey initial afterKey).mem.readAt
      ((Wrapper.keySlot initial).add 32#64) 1280 = value := by
  have hsrc := Dalek.smallRange_add hm.resultRange (k := 8) (count := 192) (by decide)
  have hread := MemoryState.readAt_add_of_readAt (off := 32#64) hsrc.fits
    (hsrc.no_wrap (k := 32) (by decide)) (w := 1280) (by decide) rfl
  have hadd : ((Wrapper.keyResultSlot initial).add 8#64).add 32#64 =
      (Wrapper.keyResultSlot initial).add 40#64 := by
    simp [Pointer.add, BitVec.add_assoc]
  rw [hadd, hp] at hread
  have hn : ¬(Wrapper.keySlot initial).offset.uaddOverflow 32#64 := by
    simp [Wrapper.keySlot, GlobalState.allocaPtr, BitVec.uaddOverflow]
  exact (MemoryState.readAt_storeAt_add hm.destinationFits hn (by decide)
    (afterKey.mem.readAt ((Wrapper.keyResultSlot initial).add 8#64) 1536)).trans hread.symm

/-- The signature destination is a distinct wrapper allocation, so neither
32-byte signature store changes the cached point. -/
theorem afterSignature_point (i : Invocation) (initial decoded : GlobalState)
    (x t : Key.Words) (value : BitVec 1280)
    (hm : Wrapper.KeyMemory initial (WrapperKeyLink.afterKey initial decoded i x t true))
    (hp : (WrapperKeyLink.afterKey initial decoded i x t true).mem.readAt
      ((Wrapper.keyResultSlot initial).add 40#64) 1280 = value) :
    (LinkedLeaves.afterSignature i initial decoded x t true).mem.readAt
      ((Wrapper.keySlot initial).add 32#64) 1280 = value := by
  unfold LinkedLeaves.afterSignature
  rw [Signature.copied_read_frame]
  · exact copiedKey_point initial _ value hm hp
  · simp [Wrapper.signatureSlot, Wrapper.keySlot, GlobalState.allocaPtr,
      GlobalState.alloca, Pointer.add]
    omega

/-- Signature-copy conditions and the remaining Dalek entry memory, with the
cached point omitted. No constructor-output equality is assumed. -/
structure SignatureMemoryExceptPoint (dg : Dalek.Globals) (cg : Challenge.Globals)
    (layout : Dalek.Layout Point Scalar Result) (i : Invocation) (initial decoded : GlobalState)
    (x t : Key.Words) (valid : Bool) (a r s : Bytes32) (minusA : Point)
    (message : List (BitVec 8)) : Prop where
  destinationFits : Fits decoded.mem (Wrapper.keySlot initial) 1536
  wellFormed : (Wrapper.copiedKey initial (WrapperKeyLink.afterKey initial decoded i x t valid)).WF
  signatureDestination : SmallRange
    (Wrapper.copiedKey initial (WrapperKeyLink.afterKey initial decoded i x t valid)).mem
    (Wrapper.signatureSlot initial) 64
  signatureSource : SmallRange
    (Wrapper.copiedKey initial (WrapperKeyLink.afterKey initial decoded i x t valid)).mem i.signature 64
  signatureDisjoint : (Wrapper.signatureSlot initial).id ≠ i.signature.id
  memory : EntryMemoryExceptPoint dg cg layout (LinkedLeaves.afterSignature i initial decoded x t valid)
    (Wrapper.keySlot initial) (Wrapper.signatureSlot initial) i.message a r s minusA message

/-- Raw decoder coordinate bytes suffice to recover the previously assumed
post-copy cached-minus-A field, for the concrete limb layout. -/
theorem signatureMemory_of_decoder
    (kp : Key.Primitives) (dg : Dalek.Globals) (cg : Challenge.Globals)
    (base : Dalek.Layout Key.PointWords Scalar Result) (shared : Shared Key.PointWords Scalar)
    (hnegate : shared.negate = Key.PointWords.negate)
    (i : Invocation) (initial decoded : GlobalState) (A : Key.PointWords)
    (a r s : Bytes32) (message : List (BitVec 8))
    (hd : Key.DecoderCall kp (Wrapper.allocated initial) decoded (Wrapper.keyResultSlot initial)
      i.publicKey A.X A.T true)
    (hy : decoded.mem.readAt ((Key.optionSlot (Wrapper.allocated initial)).add 48#64) 320 =
      Key.coordinatePayload A.Y)
    (hz : decoded.mem.readAt ((Key.optionSlot (Wrapper.allocated initial)).add 88#64) 320 =
      Key.coordinatePayload A.Z)
    (hm : SignatureMemoryExceptPoint dg cg (Key.limbLayout base) i initial decoded A.X A.T true
      a r s (shared.negate A) message) :
    LinkedLeaves.SignatureMemory dg cg (Key.limbLayout base) i initial decoded A.X A.T true
      a r s (shared.negate A) message := by
  have hcaller : (Wrapper.keyResultSlot initial).id.id <
      (Wrapper.allocated initial).alloc.nextFreeBlock := by
    simp [Wrapper.keyResultSlot, Wrapper.allocated, GlobalState.allocaPtr, GlobalState.alloca]
  have hp := (Key.call_shared_cached_point kp (Wrapper.allocated initial) decoded
    (Wrapper.keyResultSlot initial) i.publicKey A base shared hnegate hd hy hz hcaller).2
  have hread := afterSignature_point i initial decoded A.X A.T _
    (WrapperKeyLink.key_memory hd.outputRange hm.destinationFits) hp
  have hrange := Dalek.smallRange_add hm.memory.keyRange (k := 32) (count := 160) (by decide)
  exact ⟨hm.destinationFits, hm.wellFormed, hm.signatureDestination, hm.signatureSource,
    hm.signatureDisjoint, hm.memory.complete ⟨hrange, hread⟩⟩

/-- Decoder representatives are identified only on the successful branch.
Malformed keys retain the unconditional rejection path. -/
def Inputs (kp : Key.Primitives) (dg : Dalek.Globals) (cg : Challenge.Globals)
    (base : Dalek.Layout Key.PointWords Scalar Result) (shared : Shared Key.PointWords Scalar)
    (i : Invocation) (initial : GlobalState) (a r s : Bytes32) (message : List (BitVec 8)) : Prop :=
  i.length = BitVec.ofNat 64 message.length ∧
  ∃ decoded x t,
    Key.DecoderCall kp (Wrapper.allocated initial) decoded (Wrapper.keyResultSlot initial)
      i.publicKey x t (shared.decompress a).isSome ∧
    ∀ A, shared.decompress a = some A →
      x = A.X ∧ t = A.T ∧
      decoded.mem.readAt ((Key.optionSlot (Wrapper.allocated initial)).add 48#64) 320 =
        Key.coordinatePayload A.Y ∧
      decoded.mem.readAt ((Key.optionSlot (Wrapper.allocated initial)).add 88#64) 320 =
        Key.coordinatePayload A.Z ∧
      SignatureMemoryExceptPoint dg cg (Key.limbLayout base) i initial decoded x t
        (shared.decompress a).isSome a r s (shared.negate A) message

/-- The exact-signature input package is constructed after deriving its
cached-point byte relation from the decoder and both actual copies. -/
theorem exactSignatureInputs_of_decoder
    (kp : Key.Primitives) (dg : Dalek.Globals) (cg : Challenge.Globals)
    (base : Dalek.Layout Key.PointWords Scalar Result) (shared : Shared Key.PointWords Scalar)
    (hnegate : shared.negate = Key.PointWords.negate)
    (i : Invocation) (initial : GlobalState) (a r s : Bytes32) (message : List (BitVec 8))
    (h : Inputs kp dg cg base shared i initial a r s message) :
    LinkedLeaves.ExactSignatureInputs kp dg cg (Key.limbLayout base) shared i initial a r s message := by
  obtain ⟨hlen, decoded, x, t, hd, hm⟩ := h
  refine ⟨hlen, decoded, x, t, hd, ?_⟩
  intro A hA
  obtain ⟨hx, ht, hy, hz, hmem⟩ := hm A hA
  subst x t
  have hd' : Key.DecoderCall kp (Wrapper.allocated initial) decoded (Wrapper.keyResultSlot initial)
      i.publicKey A.X A.T true := by simpa [hA] using hd
  have hmem' : SignatureMemoryExceptPoint dg cg (Key.limbLayout base) i initial decoded A.X A.T true
      a r s (shared.negate A) message := by simpa [hA] using hmem
  simpa [hA] using signatureMemory_of_decoder kp dg cg base shared hnegate
    i initial decoded A a r s message hd' hy hz hmem'

/-- Exact execution for the concrete limb representation, with the cached
point derived and the signature constructor linked to its imported body. -/
theorem observe_of_decoder {Scalar Result : Type}
    (kp : Key.Primitives) (dp : Dalek.Primitives) (dg : Dalek.Globals)
    (cp : Challenge.Primitives) (cg : Challenge.Globals) (sha : Challenge.Sha512Model)
    (base : Dalek.Layout Key.PointWords Scalar Result) (shared : Shared Key.PointWords Scalar)
    (hnegate : shared.negate = Key.PointWords.negate)
    (doubleBase : Scalar → Key.PointWords → Scalar → Result) (compress : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (contracts : Dalek.LeafContracts dp dg (Key.limbLayout base) shared doubleBase compress)
    (hlink : dp.challengeScalar = (Challenge.program cp cg).call)
    (hcompress : Challenge.CompressContract cp.sha512Compress sha)
    (hscalar : Challenge.ScalarFromSha512Contract cp.scalarFromSha512 sha)
    (hencoding : ∀ r a msg, base.scalar (challenge r a msg) =
      Challenge.digestScalarBytes (sha.digest (Challenge.transcript r a msg)))
    (hidentity : base.identity = Dalek.identityBytes)
    (i : Invocation) (initial : GlobalState) (a r s : Bytes32) (message : List (BitVec 8))
    (h : Inputs kp dg cg base shared i initial a r s message) :
    Execution.observe (linkedWrapper kp dp dg Signature.program.call) i initial =
      some (verify shared doubleBase compress a r s (challenge r a message)) :=
  LinkedLeaves.observe_exact_signature kp dp dg cp cg sha Signature.program.call
    (Key.limbLayout base) shared doubleBase compress challenge contracts hlink hcompress hscalar
    hencoding hidentity rfl i initial a r s message
    (exactSignatureInputs_of_decoder kp dg cg base shared hnegate i initial a r s message h)

end Agave.Ed25519.Verifier.Execution.LinkedConcretePayload

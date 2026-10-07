import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionLinked
import SSA.Projects.Agave.Ed25519.Proof.Verifier.WrapperKeyLink
import SSA.Projects.Agave.Ed25519.Proof.Verifier.SignatureExecution

/-!
# Exact Agave wrapper and callee composition

The wrapper, key constructor, signature constructor, Dalek verifier and
challenge use their actual fuel-independent RIR call semantics. The exact
signature endpoint retains the decoder ABI, the two SHA leaf contracts, and
Dalek's named leaves as semantic assumptions.
The constructor/signature memory-to-point-layout relation remains explicit in
`SignatureContinuation.memory`; this module does not claim that relation is
already derived from arbitrary decoder output limbs.
-/
namespace Agave.Ed25519.Verifier.Execution.LinkedLeaves
open LeanMLIR.RIR

/-- The signature copy's exact call and the concrete memory presented to Dalek.
The memory fields contain neither execution nor acceptance predicates. -/
structure SignatureContinuation (signatureFromBytes : Vals [.ptr, .ptr] → EffectM (Vals []))
    (dg : Dalek.Globals) (cg : Challenge.Globals) (layout : Dalek.Layout Point Scalar Result)
    (i : Invocation) (initial decoded afterSignature : GlobalState)
    (x t : Key.Words) (valid : Bool) (a r s : Bytes32) (minusA : Point)
    (message : List (BitVec 8)) : Prop where
  destinationFits : Fits decoded.mem (Wrapper.keySlot initial) 1536
  signature : signatureFromBytes (Wrapper.ptrArgs (Wrapper.signatureSlot initial) i.signature)
    (Wrapper.copiedKey initial (WrapperKeyLink.afterKey initial decoded i x t valid)) =
      .value (.nil, afterSignature)
  memory : Dalek.EntryMemory dg cg layout afterSignature (Wrapper.keySlot initial)
    (Wrapper.signatureSlot initial) i.message a r s minusA message

/-- Per-invocation leaf and memory inputs. Invalid public keys need no
signature execution or Dalek memory premise. -/
def Inputs (kp : Key.Primitives)
    (signatureFromBytes : Vals [.ptr, .ptr] → EffectM (Vals []))
    (dg : Dalek.Globals) (cg : Challenge.Globals) (layout : Dalek.Layout Point Scalar Result)
    (shared : Shared Point Scalar) (i : Invocation) (initial : GlobalState)
    (a r s : Bytes32) (message : List (BitVec 8)) : Prop :=
  i.length = BitVec.ofNat 64 message.length ∧
  ∃ decoded x t,
    Key.DecoderCall kp (Wrapper.allocated initial) decoded (Wrapper.keyResultSlot initial)
      i.publicKey x t (shared.decompress a).isSome ∧
    ∀ A, shared.decompress a = some A → ∃ afterSignature,
      SignatureContinuation signatureFromBytes dg cg layout i initial decoded afterSignature
        x t (shared.decompress a).isSome a r s (shared.negate A) message

/-- The exact state produced by the imported signature constructor. -/
def afterSignature (i : Invocation) (initial decoded : GlobalState)
    (x t : Key.Words) (valid : Bool) : GlobalState :=
  Signature.copied (Wrapper.copiedKey initial
    (WrapperKeyLink.afterKey initial decoded i x t valid)) (Wrapper.signatureSlot initial) i.signature

/-- Memory-only preconditions for the imported signature copy, together with
its post-copy Dalek entry relation. There is no signature execution premise. -/
structure SignatureMemory (dg : Dalek.Globals) (cg : Challenge.Globals)
    (layout : Dalek.Layout Point Scalar Result) (i : Invocation) (initial decoded : GlobalState)
    (x t : Key.Words) (valid : Bool) (a r s : Bytes32) (minusA : Point)
    (message : List (BitVec 8)) : Prop where
  destinationFits : Fits decoded.mem (Wrapper.keySlot initial) 1536
  wellFormed : (Wrapper.copiedKey initial (WrapperKeyLink.afterKey initial decoded i x t valid)).WF
  signatureDestination : Reduce64.Execution.SmallRange
    (Wrapper.copiedKey initial (WrapperKeyLink.afterKey initial decoded i x t valid)).mem
    (Wrapper.signatureSlot initial) 64
  signatureSource : Reduce64.Execution.SmallRange
    (Wrapper.copiedKey initial (WrapperKeyLink.afterKey initial decoded i x t valid)).mem i.signature 64
  signatureDisjoint : (Wrapper.signatureSlot initial).id ≠ i.signature.id
  memory : Dalek.EntryMemory dg cg layout (afterSignature i initial decoded x t valid)
    (Wrapper.keySlot initial) (Wrapper.signatureSlot initial) i.message a r s minusA message

/-- The signature continuation's execution equation follows from the linked
constructor body; only its explicit memory relation is retained. -/
theorem SignatureMemory.continuation
    (signatureFromBytes : Vals [.ptr, .ptr] → EffectM (Vals []))
    (hlink : signatureFromBytes = Signature.program.call)
    (h : SignatureMemory dg cg layout i initial decoded x t valid a r s minusA message) :
    SignatureContinuation signatureFromBytes dg cg layout i initial decoded
      (afterSignature i initial decoded x t valid) x t valid a r s minusA message := by
  refine ⟨h.destinationFits, ?_, h.memory⟩
  rw [hlink]
  exact Signature.wrapper_signature i initial _ h.wellFormed h.signatureDestination
    h.signatureSource h.signatureDisjoint

/-- All implementation-level call inputs after also deriving the signature
constructor's execution from its exact body. -/
def ExactSignatureInputs (kp : Key.Primitives)
    (dg : Dalek.Globals) (cg : Challenge.Globals) (layout : Dalek.Layout Point Scalar Result)
    (shared : Shared Point Scalar) (i : Invocation) (initial : GlobalState)
    (a r s : Bytes32) (message : List (BitVec 8)) : Prop :=
  i.length = BitVec.ofNat 64 message.length ∧
  ∃ decoded x t,
    Key.DecoderCall kp (Wrapper.allocated initial) decoded (Wrapper.keyResultSlot initial)
      i.publicKey x t (shared.decompress a).isSome ∧
    ∀ A, shared.decompress a = some A →
      SignatureMemory dg cg layout i initial decoded x t (shared.decompress a).isSome
        a r s (shared.negate A) message

theorem inputs_of_exact_signature
    (signatureFromBytes : Vals [.ptr, .ptr] → EffectM (Vals []))
    (hlink : signatureFromBytes = Signature.program.call)
    (h : ExactSignatureInputs kp dg cg layout shared i initial a r s message) :
    Inputs kp signatureFromBytes dg cg layout shared i initial a r s message := by
  obtain ⟨hlen, decoded, x, t, hdecoder, hmemory⟩ := h
  refine ⟨hlen, decoded, x, t, hdecoder, ?_⟩
  intro A hA
  exact ⟨_, (hmemory A hA).continuation signatureFromBytes hlink⟩

section
variable {Point Scalar Result : Type}
variable (kp : Key.Primitives) (dp : Dalek.Primitives) (dg : Dalek.Globals)
variable (cp : Challenge.Primitives) (cg : Challenge.Globals) (sha : Challenge.Sha512Model)
variable (signatureFromBytes : Vals [.ptr, .ptr] → EffectM (Vals []))
variable (layout : Dalek.Layout Point Scalar Result) (shared : Shared Point Scalar)
variable (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
variable (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
variable (contracts : Dalek.LeafContracts dp dg layout shared doubleBase compress)
variable (hlink : dp.challengeScalar = (Challenge.program cp cg).call)
variable (hcompress : Challenge.CompressContract cp.sha512Compress sha)
variable (hscalar : Challenge.ScalarFromSha512Contract cp.scalarFromSha512 sha)
variable (hencoding : ∀ r a msg, layout.scalar (challenge r a msg) =
  Challenge.digestScalarBytes (sha.digest (Challenge.transcript r a msg)))
variable (hidentity : layout.identity = Dalek.identityBytes)

include contracts hlink hcompress hscalar hencoding hidentity

/-- Constructs, rather than assumes, all whole-callee obligations of the
wrapper. In particular neither `Wrapper.KeyCall` nor `ChallengeContract`
appears among the hypotheses. -/
theorem primitive_calls (i : Invocation) (initial : GlobalState)
    (a r s : Bytes32) (message : List (BitVec 8))
    (h : Inputs kp signatureFromBytes dg cg layout shared i initial a r s message) :
    Wrapper.PrimitiveCalls (linkedWrapper kp dp dg signatureFromBytes) shared
      doubleBase compress challenge i initial a r s message := by
  obtain ⟨hlen, decoded, x, t, hdecoder, hsignature⟩ := h
  have hk := Key.wrapper_keyCall kp (linkedWrapper kp dp dg signatureFromBytes) shared
    i initial decoded a x t rfl hdecoder
  cases ha : shared.decompress a with
  | none =>
    refine ⟨_, decoded, decoded, hk, ?_⟩
    intro A hA
    rw [ha] at hA
    cases hA
  | some A =>
    obtain ⟨afterSignature, hs⟩ := hsignature A ha
    obtain ⟨afterDalek, hd⟩ := Dalek.program_call_of_leaf_contracts dp dg layout shared
      doubleBase compress challenge contracts cp cg sha hlink hcompress hscalar hencoding
      hidentity afterSignature (Wrapper.keySlot initial) (Wrapper.signatureSlot initial)
      i.message a r s (shared.negate A) message hs.memory
    refine ⟨_, afterSignature, afterDalek, hk, ?_⟩
    intro B hB
    have hBA : B = A := Option.some.inj (hB.symm.trans ha)
    subst B
    refine ⟨WrapperKeyLink.key_memory hdecoder.outputRange hs.destinationFits, hs.signature, ?_⟩
    simpa only [linkedWrapper, Wrapper.dalekArgs, Dalek.inputArgs, hlen,
      Dalek.code, resultCode] using hd

/-- The actual byte-input wrapper returns the control-flow specification for
all bytes, under only named leaves and explicit intermediate memory layout. -/
theorem observe (i : Invocation) (initial : GlobalState)
    (a r s : Bytes32) (message : List (BitVec 8))
    (h : Inputs kp signatureFromBytes dg cg layout shared i initial a r s message) :
    Execution.observe (linkedWrapper kp dp dg signatureFromBytes) i initial =
      some (verify shared doubleBase compress a r s (challenge r a message)) :=
  Wrapper.observe_of_primitive_calls (linkedWrapper kp dp dg signatureFromBytes) shared
    doubleBase compress challenge i initial a r s message
    (primitive_calls kp dp dg cp cg sha signatureFromBytes layout shared doubleBase compress
      challenge contracts hlink hcompress hscalar hencoding hidentity i initial a r s message h)

/-- Universal refinement is derived from leaf readiness at each representable
invocation. No whole-program refinement is retained as an assumption. -/
theorem refines (environment : Invocation → GlobalState → Prop)
    (hready : ∀ i state a r s message, Represents i state a r s message →
      environment i state → Inputs kp signatureFromBytes dg cg layout shared i state a r s message) :
    RefinesControlFlow (linkedWrapper kp dp dg signatureFromBytes) shared doubleBase compress
      challenge environment := by
  intro i state a r s message hinput henv
  exact observe kp dp dg cp cg sha signatureFromBytes layout shared doubleBase compress challenge
    contracts hlink hcompress hscalar hencoding hidentity i state a r s message
    (hready i state a r s message hinput henv)

/-- Observation with the actual signature constructor linked as well. The
remaining per-input hypotheses contain only the decoder leaf call and memory,
including the explicit cached-minus-A point representation after both copies. -/
theorem observe_exact_signature (hsignatureLink : signatureFromBytes = Signature.program.call)
    (i : Invocation) (initial : GlobalState) (a r s : Bytes32) (message : List (BitVec 8))
    (h : ExactSignatureInputs kp dg cg layout shared i initial a r s message) :
    Execution.observe (linkedWrapper kp dp dg signatureFromBytes) i initial =
      some (verify shared doubleBase compress a r s (challenge r a message)) :=
  observe kp dp dg cp cg sha signatureFromBytes layout shared doubleBase compress challenge
    contracts hlink hcompress hscalar hencoding hidentity i initial a r s message
    (inputs_of_exact_signature signatureFromBytes hsignatureLink h)

theorem refines_exact_signature (hsignatureLink : signatureFromBytes = Signature.program.call)
    (environment : Invocation → GlobalState → Prop)
    (hready : ∀ i state a r s message, Represents i state a r s message → environment i state →
      ExactSignatureInputs kp dg cg layout shared i state a r s message) :
    RefinesControlFlow (linkedWrapper kp dp dg signatureFromBytes) shared doubleBase compress
      challenge environment := by
  intro i state a r s message hinput henv
  exact observe_exact_signature kp dp dg cp cg sha signatureFromBytes layout shared doubleBase
    compress challenge contracts hlink hcompress hscalar hencoding hidentity hsignatureLink
    i state a r s message (hready i state a r s message hinput henv)

end
end Agave.Ed25519.Verifier.Execution.LinkedLeaves

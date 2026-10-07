import SSA.Projects.Agave.Ed25519.Bridge.FiredancerScalarArithmetic
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerInvocationChallenge

/-! Transfer one exact source arithmetic certificate to the existing verifier
invocation. This optional adapter imports the legacy SHA program bindings;
the independent source-arithmetic slice does not import this module. -/

namespace Agave.Ed25519.Bridge
open LeanMLIR SLLVM Firedancer Firedancer.Common

/-- The deterministic adapter used by `fd_ed25519_verify` has exactly the
same definedness and packed bytes as the explicit source expression. -/
theorem firedancerSourceReduce_packed (digest : BitVec 512) :
    (firedancerSourceReduce digest).map packWords =
      (ScalarArithmetic.sourceReduce digest).map packWords :=
  ScalarArithmetic.packed_eq firedancerSourceReduce_by ScalarArithmetic.sourceReduce_by digest

/-- A checked one-digest arithmetic certificate supplies the return witness
needed by the existing invocation constructor. -/
theorem firedancerSourceReduce_returns_of_certificate (digest : BitVec 512)
    (h : FiredancerScalarCanonicalAt digest) :
    ∃ words, firedancerSourceReduce digest = some words := by
  have heq := (firedancerSourceReduce_packed digest).trans h
  cases hw : firedancerSourceReduce digest with
  | none => simp [hw] at heq
  | some words => exact ⟨words, rfl⟩

/-- All successful source-adapter outputs at the certified digest are the
canonical residue. This is precisely the local `hvalue` invocation premise. -/
theorem firedancerSourceReduce_value_of_certificate (digest : BitVec 512)
    (h : FiredancerScalarCanonicalAt digest) (words : Fin 4 → BitVec 64)
    (hw : firedancerSourceReduce digest = some words) :
    (packWords words).toNat = hashToScalar digest := by
  have heq := (firedancerSourceReduce_packed digest).trans h
  rw [hw] at heq
  have hbytes : packWords words = Challenge.reducedBytes digest := Option.some.inj heq
  rw [hbytes, Challenge.reducedBytes_toNat]

/-- If a universal arithmetic proof supplies the source certificates, the
existing uniform challenge API follows without any additional bridge. -/
theorem firedancerSourceReduce_valueCorrect_of_certificates
    (h : ∀ digest, FiredancerScalarCanonicalAt digest) :
    Challenge.ReductionValueCorrect firedancerSourceReduce :=
  fun digest words hw => firedancerSourceReduce_value_of_certificate digest (h digest) words hw

/-- For an existing invocation using the committed source reducer, only this
invocation's digest certificate is needed to close the arithmetic premise. -/
theorem FiredancerProofInvocation.challenge_eq_of_source_certificate
    (v : FiredancerProofInvocation)
    (hsource : v.reduce = firedancerSourceReduce)
    (hash : HashBytes → BitVec 512)
    (hhash : Challenge.DigestBy ⟨v.init, v.append, v.finish⟩
      (v.state.mem.live? v.sha.id) v.sha.offset hash)
    (hcertificate : FiredancerScalarCanonicalAt v.digest) :
    v.challenge = messageChallenge hash v.r v.a v.messageBytes := by
  apply v.challenge_eq_of_digestBy_local hash hhash
  apply firedancerSourceReduce_value_of_certificate v.digest hcertificate v.words
  simpa only [hsource] using v.reduceReturns

end Agave.Ed25519.Bridge

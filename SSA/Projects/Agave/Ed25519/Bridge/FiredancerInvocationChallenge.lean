import SSA.Projects.Agave.Ed25519.Bridge.FiredancerInvocationReady
import SSA.Projects.Agave.Ed25519.Bridge.ChallengeFiredancer

/-!
The deterministic Option adapters at the Firedancer invocation boundary.
Digest and reduction witnesses are recovered from the composed challenge, or
constructed from the separate streaming/hash contract and local termination.
The source reducer's value correctness remains an arithmetic obligation: its
proved determinism theorem alone cannot establish reduction modulo L.
-/

namespace Agave.Ed25519.Bridge
open LeanMLIR SLLVM Firedancer Firedancer.Common

/-- Fresh preparation fixes the digest's only memory-dependent input. -/
theorem firedancerDigest_fresh (state : GlobalState) (calls : FiredancerHashCalls)
    (r a : BitVec 256) (msg : HashBytes) :
    firedancerDigest calls
      ((firedancerWithSha state).mem.live? (firedancerFreshSha state).id)
      (firedancerFreshSha state).offset r a msg =
      firedancerDigest calls (some { length := 256, bytes := 0#_ }) 0 r a msg := by
  rw [firedancerFreshSha_live]
  rfl

theorem firedancerChallenge_fresh (state : GlobalState) (calls : FiredancerHashCalls)
    (reduce : FiredancerReduce) (r a : BitVec 256) (msg : HashBytes) :
    firedancerChallenge calls reduce
      ((firedancerWithSha state).mem.live? (firedancerFreshSha state).id)
      (firedancerFreshSha state).offset r a msg =
      firedancerChallenge calls reduce (some { length := 256, bytes := 0#_ }) 0 r a msg := by
  rw [firedancerFreshSha_live]
  rfl

/-- Successful composed challenges contain exactly the digest and output-word
witnesses required by the existing source conformance theorem. -/
theorem firedancerChallenge_returns_iff (calls : FiredancerHashCalls)
    (reduce : FiredancerReduce) (blk : Option LiveBlock) (off : BitVec 64)
    (r a : BitVec 256) (msg : HashBytes) (challenge : Nat) :
    firedancerChallenge calls reduce blk off r a msg = some challenge ↔
      ∃ digest words,
        firedancerDigest calls blk off r a msg = some digest ∧
        reduce digest = some words ∧ firedancerReducedScalar words = challenge := by
  simp only [firedancerChallenge, Option.bind_eq_some_iff, Option.map_eq_some_iff]
  aesop

namespace FiredancerProofInvocation

/-- The stored digest is forced by the separate hash-output contract. -/
theorem digest_eq_of_digestBy (v : FiredancerProofInvocation)
    (hash : HashBytes → BitVec 512)
    (hhash : Challenge.DigestBy ⟨v.init, v.append, v.finish⟩
      (v.state.mem.live? v.sha.id) v.sha.offset hash) :
    v.digest = hash (hashTranscript v.r v.a v.messageBytes) :=
  Option.some.inj (v.digestReturns.symm.trans (hhash v.r v.a v.messageBytes))

/-- Only the value of this invocation's returned words is needed. No claim
about other inputs to the reducer enters the verification bridge. -/
theorem challenge_eq_of_digestBy_local (v : FiredancerProofInvocation)
    (hash : HashBytes → BitVec 512)
    (hhash : Challenge.DigestBy ⟨v.init, v.append, v.finish⟩
      (v.state.mem.live? v.sha.id) v.sha.offset hash)
    (hvalue : (packWords v.words).toNat = hashToScalar v.digest) :
    v.challenge = messageChallenge hash v.r v.a v.messageBytes := by
  change firedancerReducedScalar v.words = _
  rw [firedancerReducedScalar_eq_hashToScalar v.digest v.words hvalue,
    v.digest_eq_of_digestBy hash hhash]
  rfl

/-- There is no need for a second composed challenge premise once the digest
contract and reducer value theorem are available. -/
theorem challenge_eq_of_digestBy (v : FiredancerProofInvocation)
    (hash : HashBytes → BitVec 512)
    (hhash : Challenge.DigestBy ⟨v.init, v.append, v.finish⟩
      (v.state.mem.live? v.sha.id) v.sha.offset hash)
    (hreduce : Challenge.ReductionValueCorrect v.reduce) :
    v.challenge = messageChallenge hash v.r v.a v.messageBytes :=
  Challenge.returned_challenge_eq hhash hreduce v.r v.a v.messageBytes
    v.digest v.words v.digestReturns v.reduceReturns

theorem challenge_eq_of_stream (v : FiredancerProofInvocation)
    (hash : HashBytes → BitVec 512)
    (hhash : HashTranscriptRefinement ⟨v.init, v.append, v.finish⟩ hash
      (v.state.mem.live? v.sha.id) v.sha.offset)
    (hreduce : Challenge.ReductionValueCorrect v.reduce) :
    v.challenge = messageChallenge hash v.r v.a v.messageBytes :=
  v.challenge_eq_of_digestBy hash (Challenge.digestBy_of_stream hhash) hreduce

section Ready

variable (state : GlobalState) (msg : Pointer) (sz : BitVec 64) (sig pk : Pointer)
  (kbits : BitVec (80 * 64))
  (input : FiredancerInputReady state msg sz sig pk)
  (globals : FiredancerGlobalsReady state kbits)
  (calls : FiredancerHashCalls)
  (finishBlock : Option LiveBlock → BitVec 64 → Option LiveBlock → BitVec 64 → Option LiveBlock)
  (hinit : Sha512InitBy calls.init)
  (happend : Sha512AppendBy kbits calls.append)
  (hfinish : Sha512FiniBy kbits calls.finish finishBlock)

/-- Direct invocation constructor: all environment and buffer obligations are
derived from preparation, with only the local partial-call returns supplied. -/
noncomputable def ofReadyReturns (digest : BitVec 512) (words : Fin 4 → BitVec 64)
    (hdigest : firedancerDigest calls
      ((firedancerWithSha state).mem.live? (firedancerFreshSha state).id) 0
      (readBuf (input.args globals.reference.wf).sigBuf)
      (readBuf (input.args globals.reference.wf).pkBuf)
      (bytesOf (readWord (input.args globals.reference.wf).msgFits)) = some digest)
    (hwords : firedancerSourceReduce digest = some words) : FiredancerProofInvocation where
  message := msg
  size := sz
  signature := sig
  publicKey := pk
  sha := firedancerFreshSha state
  state := firedancerWithSha state
  args := input.args globals.reference.wf
  reduce := firedancerSourceReduce
  roundConstants := kbits
  init := calls.init
  append := calls.append
  finish := calls.finish
  finishBlock := finishBlock
  environment := globals.environment calls finishBlock hinit happend hfinish
  digest := digest
  words := words
  digestReturns := hdigest
  reduceReturns := hwords

/-- The digest is fixed by the hash contract. Only successful reduction on
this digest is required; uniform reducer totality is unnecessary. -/
noncomputable def ofReadyDigestBy (hash : HashBytes → BitVec 512)
    (hhash : Challenge.DigestBy calls
      ((firedancerWithSha state).mem.live? (firedancerFreshSha state).id) 0 hash)
    (hreturns : ∃ words, firedancerSourceReduce
      (hash (hashTranscript
        (readBuf (input.args globals.reference.wf).sigBuf)
        (readBuf (input.args globals.reference.wf).pkBuf)
        (bytesOf (readWord (input.args globals.reference.wf).msgFits)))) = some words) :
    FiredancerProofInvocation :=
  ofReadyReturns state msg sz sig pk kbits input globals calls finishBlock hinit happend hfinish
    _ (Classical.choose hreturns) (hhash _ _ _) (Classical.choose_spec hreturns)

theorem ofReadyDigestBy_challenge (hash : HashBytes → BitVec 512)
    (hhash : Challenge.DigestBy calls
      ((firedancerWithSha state).mem.live? (firedancerFreshSha state).id) 0 hash)
    (hreturns : ∃ words, firedancerSourceReduce
      (hash (hashTranscript
        (readBuf (input.args globals.reference.wf).sigBuf)
        (readBuf (input.args globals.reference.wf).pkBuf)
        (bytesOf (readWord (input.args globals.reference.wf).msgFits)))) = some words)
    (hreduce : Challenge.ReductionValueCorrect firedancerSourceReduce) :
    (ofReadyDigestBy state msg sz sig pk kbits input globals calls finishBlock
      hinit happend hfinish hash hhash hreturns).challenge =
      messageChallenge hash (readBuf (input.args globals.reference.wf).sigBuf)
        (readBuf (input.args globals.reference.wf).pkBuf)
        (bytesOf (readWord (input.args globals.reference.wf).msgFits)) :=
  challenge_eq_of_digestBy _ hash hhash hreduce

theorem ofReadyDigestBy_challenge_local (hash : HashBytes → BitVec 512)
    (hhash : Challenge.DigestBy calls
      ((firedancerWithSha state).mem.live? (firedancerFreshSha state).id) 0 hash)
    (hreturns : ∃ words, firedancerSourceReduce
      (hash (hashTranscript
        (readBuf (input.args globals.reference.wf).sigBuf)
        (readBuf (input.args globals.reference.wf).pkBuf)
        (bytesOf (readWord (input.args globals.reference.wf).msgFits)))) = some words)
    (hvalue : ∀ words, firedancerSourceReduce
      (hash (hashTranscript
        (readBuf (input.args globals.reference.wf).sigBuf)
        (readBuf (input.args globals.reference.wf).pkBuf)
        (bytesOf (readWord (input.args globals.reference.wf).msgFits)))) = some words →
      (packWords words).toNat = hashToScalar
        (hash (hashTranscript
          (readBuf (input.args globals.reference.wf).sigBuf)
          (readBuf (input.args globals.reference.wf).pkBuf)
          (bytesOf (readWord (input.args globals.reference.wf).msgFits))))) :
    (ofReadyDigestBy state msg sz sig pk kbits input globals calls finishBlock
      hinit happend hfinish hash hhash hreturns).challenge =
      messageChallenge hash (readBuf (input.args globals.reference.wf).sigBuf)
        (readBuf (input.args globals.reference.wf).pkBuf)
        (bytesOf (readWord (input.args globals.reference.wf).msgFits)) :=
  challenge_eq_of_digestBy_local _ hash hhash
    (hvalue (Classical.choose hreturns) (Classical.choose_spec hreturns))

include hinit happend hfinish

/-- Feed the composed challenge directly to the source theorem. Its two
return witnesses are extracted, rather than repeated as caller assumptions. -/
theorem ready_executionRefines_of_challenge (challenge : Nat)
    (hchallenge : firedancerChallenge calls firedancerSourceReduce
      ((firedancerWithSha state).mem.live? (firedancerFreshSha state).id) 0
      (readBuf (input.args globals.reference.wf).sigBuf)
      (readBuf (input.args globals.reference.wf).pkBuf)
      (bytesOf (readWord (input.args globals.reference.wf).msgFits)) = some challenge) :
    FiredancerExecutionRefines programs msg sz sig pk (firedancerFreshSha state)
      (firedancerWithSha state)
      (readBuf (input.args globals.reference.wf).pkBuf)
      (readBuf (input.args globals.reference.wf).sigBuf)
      (readBuf (input.args globals.reference.wf).sBuf) challenge := by
  obtain ⟨digest, words, hd, hw, hc⟩ := (firedancerChallenge_returns_iff ..).mp hchallenge
  rw [← hc]
  exact (ofReadyReturns state msg sz sig pk kbits input globals calls finishBlock
    hinit happend hfinish digest words hd hw).executionRefines

/-- Full source execution at the mathematical message challenge. Residual
premises are loader readiness, the three SHA call contracts and digest model,
and reduction termination/value correctness at the arithmetic boundary. -/
theorem ready_executionRefines_of_digestBy (hash : HashBytes → BitVec 512)
    (hhash : Challenge.DigestBy calls
      ((firedancerWithSha state).mem.live? (firedancerFreshSha state).id) 0 hash)
    (hreturns : ∃ words, firedancerSourceReduce
      (hash (hashTranscript
        (readBuf (input.args globals.reference.wf).sigBuf)
        (readBuf (input.args globals.reference.wf).pkBuf)
        (bytesOf (readWord (input.args globals.reference.wf).msgFits)))) = some words)
    (hreduce : Challenge.ReductionValueCorrect firedancerSourceReduce) :
    FiredancerExecutionRefines programs msg sz sig pk (firedancerFreshSha state)
      (firedancerWithSha state)
      (readBuf (input.args globals.reference.wf).pkBuf)
      (readBuf (input.args globals.reference.wf).sigBuf)
      (readBuf (input.args globals.reference.wf).sBuf)
      (messageChallenge hash (readBuf (input.args globals.reference.wf).sigBuf)
        (readBuf (input.args globals.reference.wf).pkBuf)
        (bytesOf (readWord (input.args globals.reference.wf).msgFits))) := by
  rw [← ofReadyDigestBy_challenge state msg sz sig pk kbits input globals calls
    finishBlock hinit happend hfinish hash hhash hreturns hreduce]
  exact (ofReadyDigestBy state msg sz sig pk kbits input globals calls finishBlock
    hinit happend hfinish hash hhash hreturns).executionRefines

/-- The smallest separated arithmetic boundary: both termination and value
correctness are required only at the digest of this one input transcript. -/
theorem ready_executionRefines_of_digestBy_local (hash : HashBytes → BitVec 512)
    (hhash : Challenge.DigestBy calls
      ((firedancerWithSha state).mem.live? (firedancerFreshSha state).id) 0 hash)
    (hreturns : ∃ words, firedancerSourceReduce
      (hash (hashTranscript
        (readBuf (input.args globals.reference.wf).sigBuf)
        (readBuf (input.args globals.reference.wf).pkBuf)
        (bytesOf (readWord (input.args globals.reference.wf).msgFits)))) = some words)
    (hvalue : ∀ words, firedancerSourceReduce
      (hash (hashTranscript
        (readBuf (input.args globals.reference.wf).sigBuf)
        (readBuf (input.args globals.reference.wf).pkBuf)
        (bytesOf (readWord (input.args globals.reference.wf).msgFits)))) = some words →
      (packWords words).toNat = hashToScalar
        (hash (hashTranscript
          (readBuf (input.args globals.reference.wf).sigBuf)
          (readBuf (input.args globals.reference.wf).pkBuf)
          (bytesOf (readWord (input.args globals.reference.wf).msgFits))))) :
    FiredancerExecutionRefines programs msg sz sig pk (firedancerFreshSha state)
      (firedancerWithSha state)
      (readBuf (input.args globals.reference.wf).pkBuf)
      (readBuf (input.args globals.reference.wf).sigBuf)
      (readBuf (input.args globals.reference.wf).sBuf)
      (messageChallenge hash (readBuf (input.args globals.reference.wf).sigBuf)
        (readBuf (input.args globals.reference.wf).pkBuf)
        (bytesOf (readWord (input.args globals.reference.wf).msgFits))) := by
  rw [← ofReadyDigestBy_challenge_local state msg sz sig pk kbits input globals calls
    finishBlock hinit happend hfinish hash hhash hreturns hvalue]
  exact (ofReadyDigestBy state msg sz sig pk kbits input globals calls finishBlock
    hinit happend hfinish hash hhash hreturns).executionRefines

end Ready
end FiredancerProofInvocation
end Agave.Ed25519.Bridge

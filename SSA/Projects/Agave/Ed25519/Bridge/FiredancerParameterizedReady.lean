import SSA.Projects.Agave.Ed25519.Bridge.FiredancerParameterizedSource
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerInvocationReady
import SSA.Projects.Agave.Ed25519.Bridge.ChallengeFiredancer

/-!
The source-backed preparation endpoint with arbitrary SHA program values.
Fresh allocation, global/table readiness, and the proved source reducer model
supply every non-SHA part of the original verifier proof. The endpoint has no
legacy SHA binding axioms and no whole-verifier execution premise.
-/

namespace Agave.Ed25519.Bridge
open LeanMLIR SLLVM Firedancer Firedancer.Common

section

variable (programs : FiredancerShaPrograms)
  (state : GlobalState) (msg : Pointer) (sz : BitVec 64) (sig pk : Pointer)
  (kbits : BitVec (80 * 64))
  (input : FiredancerInputReady state msg sz sig pk)
  (globals : FiredancerGlobalsReady state kbits)
  (calls : FiredancerHashCalls)
  (finishBlock : Option LiveBlock → BitVec 64 → Option LiveBlock → BitVec 64 → Option LiveBlock)
  (hinit : FiredancerShaInitBy programs calls.init)
  (happend : FiredancerShaAppendBy programs kbits calls.append)
  (hfinish : FiredancerShaFinishBy programs kbits calls.finish finishBlock)

include hinit happend hfinish

/-- The complete source execution follows from concrete preparation and the
three supplied SHA program contracts. The reducer model and table mathematics
are proved, and only this invocation's partial-call return witnesses remain. -/
theorem firedancerParameterized_ready_executionRefines
    (digest : BitVec 512) (words : Fin 4 → BitVec 64)
    (hdigest : firedancerDigest calls
      ((firedancerWithSha state).mem.live? (firedancerFreshSha state).id) 0
      (readBuf (input.args globals.reference.wf).sigBuf)
      (readBuf (input.args globals.reference.wf).pkBuf)
      (bytesOf (readWord (input.args globals.reference.wf).msgFits)) = some digest)
    (hwords : firedancerSourceReduce digest = some words) :
    FiredancerExecutionRefines programs msg sz sig pk (firedancerFreshSha state)
      (firedancerWithSha state)
      (readBuf (input.args globals.reference.wf).pkBuf)
      (readBuf (input.args globals.reference.wf).sigBuf)
      (readBuf (input.args globals.reference.wf).sBuf) (firedancerReducedScalar words) := by
  let args := input.args globals.reference.wf
  have hconforms := firedancerParameterizedSource_conforms programs msg sz sig pk
    (firedancerFreshSha state) (firedancerWithSha state)
    args.msgFits args.sigBuf args.sBuf args.pkBuf args.sigNull
    firedancerSourceReduce kbits calls.init calls.append calls.finish finishBlock
  obtain ⟨finalState, ret, hrun, _, _, _, _, _, _, hs, ha, hr, hdecoded⟩ :=
    hconforms args.sigOff args.msgOff args.shaPtr args.shaOff globals.shaConstantsWithSha
      args.shaSig args.shaPk args.shaMsg globals.referenceWithSha firedancerSourceReduce_by
      hinit happend hfinish firedancerBaseTable globals.baseTableWithSha
      firedancerBaseTable_values digest hdigest words hwords
  refine ⟨finalState, ret, ?_, hs, ha, hr, ?_⟩
  · simpa only [firedancerRun, firedancerParameterizedProgram_eq] using hrun
  · intro hs A R hA hR
    obtain ⟨hAlo, hRlo, heq⟩ := hdecoded hs A R hA hR
    exact ⟨hAlo, hRlo, fun hnA hnR => (heq hnA hnR).1⟩

/-- Only the hash contract and this digest's source reduction result/value
remain at the cryptographic boundary. The digest and challenge return
equations themselves follow from those separate contracts. -/
theorem firedancerParameterized_ready_executionRefines_of_digestBy
    (hash : HashBytes → BitVec 512)
    (hhash : Challenge.DigestBy calls
      (some { length := 256, bytes := 0#_ }) 0 hash)
    (hreduce : ∃ words,
      firedancerSourceReduce
        (hash (hashTranscript
          (readBuf (input.args globals.reference.wf).sigBuf)
          (readBuf (input.args globals.reference.wf).pkBuf)
          (bytesOf (readWord (input.args globals.reference.wf).msgFits)))) = some words ∧
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
  obtain ⟨words, hw, hv⟩ := hreduce
  have hscalar := firedancerReducedScalar_eq_hashToScalar _ words hv
  rw [← show firedancerReducedScalar words =
      messageChallenge hash (readBuf (input.args globals.reference.wf).sigBuf)
        (readBuf (input.args globals.reference.wf).pkBuf)
        (bytesOf (readWord (input.args globals.reference.wf).msgFits)) from hscalar]
  apply firedancerParameterized_ready_executionRefines programs state msg sz sig pk kbits
    input globals calls finishBlock hinit happend hfinish _ words ?_ hw
  rw [firedancerFreshSha_live]
  exact hhash _ _ _

end
end Agave.Ed25519.Bridge

import SSA.Projects.Agave.Ed25519.Bridge.FiredancerReachableSource
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerInvocationReady
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerScalarSourceCorrect

namespace Agave.Ed25519.Bridge
open LeanMLIR SLLVM Firedancer Firedancer.Common

/-- A proved legacy initializer contract can supply the first reachable call.
This adapter does not impose a contract on unreachable append/finish states. -/
theorem firedancerReachableInit_of_initBy (programs : FiredancerShaPrograms)
    (init : Option LiveBlock → BitVec 64 → Option (Option LiveBlock))
    (hinit : FiredancerShaInitBy programs init)
    (before after : Option LiveBlock) (off : BitVec 64)
    (hret : init before off = some after) :
    FiredancerReachableInit programs before after off := by
  intro sha s hwf hsha hoff hbefore
  apply (hinit sha s hwf hsha).1 after
  simpa only [hoff, hbefore] using hret

/-- Fresh preparation preserves the caller's signed object-size bounds. -/
theorem FiredancerReachableMemoryReady.withSha
    {state : GlobalState} {msg sig pk : Pointer} {sz : BitVec 64}
    {kbits : BitVec (80 * 64)}
    (small : FiredancerReachableMemoryReady state msg sig pk)
    (input : FiredancerInputReady state msg sz sig pk)
    (globals : FiredancerGlobalsReady state kbits) :
    FiredancerReachableMemoryReady (firedancerWithSha state) msg sig pk := by
  have carry {p : Pointer} {n : Nat} (fit : Fits state.mem p n)
      (sm : FiredancerBlockSmall state.mem p.id) :
      FiredancerBlockSmall (firedancerWithSha state).mem p.id := by
    unfold FiredancerBlockSmall
    change ∀ b, (state.afterAlloca (256 * 8)).mem.live? p.id = some b → _
    rw [live?_afterAlloca_of_fits globals.reference.wf _ fit]
    exact sm
  refine ⟨carry input.message small.message, carry input.signature small.signature,
    carry input.publicKey.1 small.publicKey, ?_⟩
  obtain ⟨q, hp, hfit, _⟩ := globals.shaConstants
  intro q' hq'
  have hq : GlobalPtr state "fd_sha512_core_ref.K" q' := hq'
  have heq : q' = q := Option.some.inj (hq.symm.trans hp)
  subst q'
  exact carry hfit (small.constants q hp)

/-- Ordinary preparation supplies the environment, fresh SHA context, base
point table, and actual scalar reducer. Exactly five reachable SHA execution
contracts remain. The scalar result and value are derived for this digest. -/
theorem firedancerReachable_ready_executionRefines
    (programs : FiredancerShaPrograms)
    (state : GlobalState) (msg : Pointer) (sz : BitVec 64) (sig pk : Pointer)
    (kbits : BitVec (80 * 64))
    (input : FiredancerInputReady state msg sz sig pk)
    (globals : FiredancerGlobalsReady state kbits)
    (small : FiredancerReachableMemoryReady state msg sig pk)
    (digest : BitVec 512)
    (calls : FiredancerReachableCalls programs kbits
      (some { length := 256, bytes := 0#_ }) 0
      (readBuf (input.args globals.reference.wf).sigBuf)
      (readBuf (input.args globals.reference.wf).pkBuf)
      (bytesOf (readWord (input.args globals.reference.wf).msgFits)) digest) :
    FiredancerExecutionRefines programs msg sz sig pk (firedancerFreshSha state)
      (firedancerWithSha state)
      (readBuf (input.args globals.reference.wf).pkBuf)
      (readBuf (input.args globals.reference.wf).sigBuf)
      (readBuf (input.args globals.reference.wf).sBuf) (hashToScalar digest) := by
  let args := input.args globals.reference.wf
  obtain ⟨words, hw, hv⟩ := firedancerSourceReduce_correct digest
  rw [← firedancerReducedScalar_eq_hashToScalar digest words hv]
  have hinit : FiredancerReachableInit programs
      ((firedancerWithSha state).mem.live? (firedancerFreshSha state).id)
      calls.initialized (firedancerFreshSha state).offset := by
    rw [firedancerFreshSha_live]
    exact calls.init
  have hconforms := firedancerReachableSource_conforms programs msg sz sig pk
    (firedancerFreshSha state) (firedancerWithSha state)
    args.msgFits args.sigBuf args.sBuf args.pkBuf args.sigNull
    firedancerSourceReduce kbits calls.initialized calls.afterR calls.afterA
    calls.afterMessage digest
  obtain ⟨finalState, ret, hrun, _, _, _, _, _, hs, ha, hr, hdecoded⟩ :=
    hconforms args.sigOff args.msgOff args.shaPtr args.shaOff globals.shaConstantsWithSha
      args.shaSig args.shaPk args.shaMsg globals.referenceWithSha
      (small.withSha input globals) firedancerSourceReduce_by
      hinit calls.appendR calls.appendA calls.appendMessage calls.finish
      firedancerBaseTable globals.baseTableWithSha firedancerBaseTable_values words hw
  refine ⟨finalState, ret, ?_, hs, ha, hr, ?_⟩
  · exact hrun
  · intro hs A R hA hR
    obtain ⟨hAlo, hRlo, heq⟩ := hdecoded hs A R hA hR
    exact ⟨hAlo, hRlo, fun hnA hnR => (heq hnA hnR).1⟩

/-- The exact acceptance policy of the reachable source invocation. In
particular choosing `digest` to be the proved SHA transcript digest requires
only the five concrete call proofs above, not a new digest-equality premise. -/
theorem firedancerReachable_ready_success_iff
    (programs : FiredancerShaPrograms)
    (state : GlobalState) (msg : Pointer) (sz : BitVec 64) (sig pk : Pointer)
    (kbits : BitVec (80 * 64))
    (input : FiredancerInputReady state msg sz sig pk)
    (globals : FiredancerGlobalsReady state kbits)
    (small : FiredancerReachableMemoryReady state msg sig pk)
    (digest : BitVec 512)
    (calls : FiredancerReachableCalls programs kbits
      (some { length := 256, bytes := 0#_ }) 0
      (readBuf (input.args globals.reference.wf).sigBuf)
      (readBuf (input.args globals.reference.wf).pkBuf)
      (bytesOf (readWord (input.args globals.reference.wf).msgFits)) digest) :
    firedancerObserve programs msg sz sig pk (firedancerFreshSha state)
      (firedancerWithSha state) = some FD_ED25519_SUCCESS ↔
      FiredancerAccept
        (readBuf (input.args globals.reference.wf).pkBuf)
        (readBuf (input.args globals.reference.wf).sigBuf)
        (readBuf (input.args globals.reference.wf).sBuf).toNat (hashToScalar digest) :=
  firedancerObserve_success_iff programs msg sz sig pk (firedancerFreshSha state)
    (firedancerWithSha state) _ _ _ _
    (firedancerReachable_ready_executionRefines programs state msg sz sig pk kbits
      input globals small digest calls)

/-- The sole acceptance-policy difference is the canonical R check, now
connected to source execution through reachable hash calls. -/
theorem agave_iff_firedancerReachable_ready_and_canonical
    (programs : FiredancerShaPrograms)
    (state : GlobalState) (msg : Pointer) (sz : BitVec 64) (sig pk : Pointer)
    (kbits : BitVec (80 * 64))
    (input : FiredancerInputReady state msg sz sig pk)
    (globals : FiredancerGlobalsReady state kbits)
    (small : FiredancerReachableMemoryReady state msg sig pk)
    (digest : BitVec 512)
    (calls : FiredancerReachableCalls programs kbits
      (some { length := 256, bytes := 0#_ }) 0
      (readBuf (input.args globals.reference.wf).sigBuf)
      (readBuf (input.args globals.reference.wf).pkBuf)
      (bytesOf (readWord (input.args globals.reference.wf).msgFits)) digest) :
    AgaveStrictAccept
      (readBuf (input.args globals.reference.wf).pkBuf)
      (readBuf (input.args globals.reference.wf).sigBuf)
      (readBuf (input.args globals.reference.wf).sBuf).toNat (hashToScalar digest) ↔
      firedancerObserve programs msg sz sig pk (firedancerFreshSha state)
        (firedancerWithSha state) = some FD_ED25519_SUCCESS ∧
      CanonicalY (readBuf (input.args globals.reference.wf).sigBuf) :=
  agave_iff_firedancerObserve_success_and_canonical programs msg sz sig pk
    (firedancerFreshSha state) (firedancerWithSha state) _ _ _ _
    (firedancerReachable_ready_executionRefines programs state msg sz sig pk kbits
      input globals small digest calls)

end Agave.Ed25519.Bridge

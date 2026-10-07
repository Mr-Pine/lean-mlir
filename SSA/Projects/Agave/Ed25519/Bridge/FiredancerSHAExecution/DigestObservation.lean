import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.Linked
import SSA.Projects.Agave.Ed25519.Bridge.ChallengeFiredancer
import SSA.Projects.Agave.Ed25519.Proof.SHA512.CompressionFold

/-! The smallest cross-IR SHA boundary is an observation of the 64 output
bytes. This module executes the actual imported RIR calls in verifier order;
it does not replace them by a SHA oracle or identify RIR and SLLVM states.
Correctness of nonempty append/core/finalization remains an explicit premise.
The observer is a semantic call composition, not a newly claimed source CFG. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution
open LeanMLIR.RIR
attribute [local instance] Classical.propDecidable

/-- Addresses used by the five SHA calls of one verifier invocation. -/
structure TranscriptInvocation where
  initial : GlobalState
  constants : Pointer
  context : Pointer
  signature : Pointer
  publicKey : Pointer
  message : Pointer
  size : BitVec 64
  output : Pointer

namespace TranscriptInvocation

/-- Exact imported init, append(R), append(A), append(M), finish calls.
Each append and finish links the actual imported scalar core. -/
noncomputable def run (v : TranscriptInvocation) :
    LeanMLIR.RIR.PoisonOr (Vals [.ptr] × GlobalState) :=
  (do
    let _ ← Init.program.call (Init.program.args (.value v.context))
    let _ ← (appendProgram v.constants).call
      (Append.program.args (.value v.context) (.value v.signature) (.value 32#64))
    let _ ← (appendProgram v.constants).call
      (Append.program.args (.value v.context) (.value v.publicKey) (.value 32#64))
    let _ ← (appendProgram v.constants).call
      (Append.program.args (.value v.context) (.value v.message) (.value v.size))
    (finishProgram v.constants).call
      (Finish.program.args (.value v.context) (.value v.output))) v.initial

/-- Retain failure, poison return values, incorrect return pointers and invalid
output reads as `none`; otherwise read exactly 64 bytes in address order. -/
noncomputable def observe (v : TranscriptInvocation) : Option (BitVec 512) :=
  match v.run with
  | .poison => none
  | .value (.cons .poison .nil, _) => none
  | .value (.cons (.value returned) .nil, after) =>
    if returned = v.output ∧ Fits after.mem v.output 512 then
      some (after.mem.readAt v.output 512)
    else none

/-- Pointwise correctness against the independently defined SHA-512 spec.
The actual machine-length invocation is explicit. There is no claim that a
64-bit length can encode every mathematical list. -/
def Correct (v : TranscriptInvocation) (r a : BitVec 256) (msg : HashBytes) : Prop :=
  v.observe = some (SHA512.digest SHA512.Spec.compression (hashTranscript r a msg))

/-- The remaining cross-IR digest simulation is equality of one observable
partial result. It makes no demand on either interpreter's final state. -/
def Simulates (v : TranscriptInvocation) (calls : FiredancerHashCalls)
    (blk : Option LeanMLIR.LiveBlock) (off : BitVec 64)
    (r a : BitVec 256) (msg : HashBytes) : Prop :=
  firedancerDigest calls blk off r a msg = v.observe

/-- Once imported RIR SHA correctness is available, this simulation is exactly
the local digest premise used by the existing SLLVM verifier theorem.
Thus full RIR/SLLVM state equivalence would be a strictly unnecessary premise. -/
theorem simulates_iff_digest (v : TranscriptInvocation)
    (calls : FiredancerHashCalls) (blk : Option LeanMLIR.LiveBlock) (off : BitVec 64)
    (r a : BitVec 256) (msg : HashBytes) (hcorrect : v.Correct r a msg) :
    v.Simulates calls blk off r a msg ↔
      firedancerDigest calls blk off r a msg =
        some (SHA512.digest SHA512.Spec.compression (hashTranscript r a msg)) := by
  unfold Simulates
  rw [hcorrect]

/-- Uniform digest correctness can also be transferred, if callers actually
supply a correct machine invocation for every mathematical transcript. The
pointwise theorem above avoids requiring this stronger representability fact. -/
theorem digestBy_of_simulates
    (calls : FiredancerHashCalls) (blk : Option LeanMLIR.LiveBlock) (off : BitVec 64)
    (invocation : BitVec 256 → BitVec 256 → HashBytes → TranscriptInvocation)
    (hcorrect : ∀ r a msg, (invocation r a msg).Correct r a msg)
    (hsim : ∀ r a msg, (invocation r a msg).Simulates calls blk off r a msg) :
    Challenge.DigestBy calls blk off (SHA512.digest SHA512.Spec.compression) := by
  intro r a msg
  exact (simulates_iff_digest _ calls blk off r a msg (hcorrect r a msg)).mp
    (hsim r a msg)

end TranscriptInvocation
end Agave.Ed25519.Bridge.FiredancerSHAExecution

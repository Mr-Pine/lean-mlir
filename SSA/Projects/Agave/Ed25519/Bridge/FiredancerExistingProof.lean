import SSA.Projects.Agave.Ed25519.Bridge.FiredancerExecution
import SSA.Projects.Firedancer.Ref.Proof.fd_ed25519_verify

/-!
Reuse the existing Firedancer conformance proof to discharge the legacy
adapter's `hconforms` premise. This module imports the original proof closure.
Its separate audit requires exactly the standard three foundations plus the
three legacy SHA bindings. The rebuilt arithmetic proof closure and this audit
passed on 2026-10-07 without native certificate dependencies.

The result instantiates the clean `FiredancerExecutionRefines` interface at the
legacy SHA bindings. Replacing those bindings with independently imported SHA
programs still requires porting the existing SHA call contracts. This theorem
does not identify arbitrary SHA programs with the signature-only legacy ones.
-/
namespace Agave.Ed25519.Bridge
open LeanMLIR SLLVM Firedancer Firedancer.Common

/-- Exact FD execution, with the whole-verifier conformance premise supplied
by the existing theorem. Remaining hypotheses are its original caller, global,
SHA/scalar leaf, and local digest/reduction termination obligations. -/
theorem firedancerExistingProof_executionRefines
    (msg : Pointer) (sz : BitVec 64) (sig pk sha : Pointer) (state : GlobalState)
    (args : VerifyArgs state msg sz sig pk sha)
    (reduce : BitVec 512 → Option (Fin 4 → BitVec 64)) (kbits : BitVec (80 * 64))
    (init : Option LiveBlock → BitVec 64 → Option (Option LiveBlock))
    (append : Option LiveBlock → BitVec 64 → List (BitVec 8) → Option (Option LiveBlock))
    (finish : Option LiveBlock → BitVec 64 → Option LiveBlock → BitVec 64 → Option (BitVec 512))
    (finishBlock : Option LiveBlock → BitVec 64 → Option LiveBlock → BitVec 64 → Option LiveBlock)
    (henv : FiredancerRefEnvironment state sha reduce kbits init append finish finishBlock)
    (digest : BitVec 512) (words : Fin 4 → BitVec 64)
    (hdigest : ed25519Digest init append finish (state.mem.live? sha.id) sha.offset
      (readBuf args.sigBuf) (readBuf args.pkBuf) (bytesOf (readWord args.msgFits)) = some digest)
    (hreduce : reduce digest = some words) :
    FiredancerExecutionRefines
      ⟨Firedancer.Common.fd_sha512_init, Firedancer.Common.fd_sha512_append,
        Firedancer.Common.fd_sha512_fini⟩
      msg sz sig pk sha state (readBuf args.pkBuf) (readBuf args.sigBuf) (readBuf args.sBuf)
      ((packWords words).toNat % 2 ^ 255) := by
  exact firedancerLegacy_executionRefines msg sz sig pk sha state args
    reduce kbits init append finish finishBlock henv
    (Firedancer.Ref.fd_ed25519_verify_conforms msg sz sig pk sha state
      args.msgFits args.sigBuf args.sBuf args.pkBuf args.sigNull
      reduce kbits init append finish finishBlock)
    digest words hdigest hreduce

/-- Data and ordinary caller/leaf premises consumed by the existing proof.
There is no verifier execution equation or return-code assertion in this
package; both follow from `executionRefines` below. -/
structure FiredancerProofInvocation where
  message : Pointer
  size : BitVec 64
  signature : Pointer
  publicKey : Pointer
  sha : Pointer
  state : GlobalState
  args : VerifyArgs state message size signature publicKey sha
  reduce : BitVec 512 → Option (Fin 4 → BitVec 64)
  roundConstants : BitVec (80 * 64)
  init : Option LiveBlock → BitVec 64 → Option (Option LiveBlock)
  append : Option LiveBlock → BitVec 64 → List (BitVec 8) → Option (Option LiveBlock)
  finish : Option LiveBlock → BitVec 64 → Option LiveBlock → BitVec 64 → Option (BitVec 512)
  finishBlock : Option LiveBlock → BitVec 64 → Option LiveBlock → BitVec 64 → Option LiveBlock
  environment : FiredancerRefEnvironment state sha reduce roundConstants init append finish finishBlock
  digest : BitVec 512
  words : Fin 4 → BitVec 64
  digestReturns : ed25519Digest init append finish (state.mem.live? sha.id) sha.offset
    (readBuf args.sigBuf) (readBuf args.pkBuf) (bytesOf (readWord args.msgFits)) = some digest
  reduceReturns : reduce digest = some words

namespace FiredancerProofInvocation

noncomputable def programs : FiredancerShaPrograms :=
  ⟨Firedancer.Common.fd_sha512_init, Firedancer.Common.fd_sha512_append,
    Firedancer.Common.fd_sha512_fini⟩

def a (v : FiredancerProofInvocation) : BitVec 256 := readBuf v.args.pkBuf
def r (v : FiredancerProofInvocation) : BitVec 256 := readBuf v.args.sigBuf
def s (v : FiredancerProofInvocation) : BitVec 256 := readBuf v.args.sBuf
def messageBytes (v : FiredancerProofInvocation) : List (BitVec 8) :=
  bytesOf (readWord v.args.msgFits)
def challenge (v : FiredancerProofInvocation) : Nat := (packWords v.words).toNat % 2 ^ 255

theorem executionRefines (v : FiredancerProofInvocation) :
    FiredancerExecutionRefines programs v.message v.size v.signature v.publicKey v.sha
      v.state v.a v.r v.s v.challenge :=
  firedancerExistingProof_executionRefines v.message v.size v.signature v.publicKey v.sha
    v.state v.args v.reduce v.roundConstants v.init v.append v.finish v.finishBlock
    v.environment v.digest v.words v.digestReturns v.reduceReturns

end FiredancerProofInvocation

end Agave.Ed25519.Bridge

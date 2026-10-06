import SSA.Projects.Agave.Ed25519.Bridge.FiredancerProgram
import SSA.Projects.Firedancer.Ref.Spec.fd_ed25519_verify

/-!
# Legacy Firedancer reference execution and acceptance

The region in this module is the existing `Firedancer.Ref.fd_ed25519_verify`,
with its actual SLLVM call and memory semantics. Only its specification is
imported. Its execution-conformance theorem is an explicit `hconforms`
premise, so this module does not depend on the unported verifier proof closure.

The SHA and scalar contracts describe partial calls and their footprints;
they do not assert SHA-512 or mathematical modular reduction. Digest/reduction
termination is supplied locally. The curve acceptance policy is then derived
from the verifier's return-path checks, rather than postulated as a separate
success-equivalence premise.

The statements in this module intentionally retain the legacy SHA constants.
Their axiom audit contains the standard three logical axioms plus exactly
`Firedancer.Common.fd_sha512_init`, `fd_sha512_append`, and `fd_sha512_fini`.
Use `FiredancerProgram`/`CrossClientExecution` for the clean parameterized
endpoint whose audit contains only the standard three.
-/

namespace Agave.Ed25519.Bridge

open LeanMLIR SLLVM Firedancer Firedancer.Common _root_.Ed25519

attribute [local irreducible] Firedancer.Ref.fd_ed25519_verify

/-- The exact existing reference verifier invocation. -/
noncomputable def firedancerRefRun (msg : Pointer) (sz : BitVec 64)
    (sig pk sha : Pointer) (state : GlobalState) :=
  StateT.run
    (runFunction (Firedancer.Ref.fd_ed25519_verify.denote
      (Ctxt.Valuation.ofHVector [.value sha, .value pk, .value sig, .value sz, .value msg]ₕ)))
    state

/-- Preserve undefined/poison execution as `none`; observe the raw return code
on a defined run. This does not identify different clients' error codes. -/
noncomputable def firedancerRefObserve (msg : Pointer) (sz : BitVec 64)
    (sig pk sha : Pointer) (state : GlobalState) : Option (BitVec 32) :=
  match firedancerRefRun msg sz sig pk sha state with
  | .poison => none
  | .value (.cons .poison .nil, _) => none
  | .value (.cons (.value ret) .nil, _) => some ret

/-- The existing FD verifier spec's environment obligations, excluding input
layout (in `VerifyArgs`) and this invocation's digest/reduction termination.
The SHA/scalar fields are the original contracts, not cryptographic claims. -/
structure FiredancerRefEnvironment (state : GlobalState) (sha : Pointer)
    (reduce : BitVec 512 → Option (Fin 4 → BitVec 64))
    (kbits : BitVec (80 * 64))
    (init : Option LiveBlock → BitVec 64 → Option (Option LiveBlock))
    (append : Option LiveBlock → BitVec 64 → List (BitVec 8) → Option (Option LiveBlock))
    (finish : Option LiveBlock → BitVec 64 → Option LiveBlock → BitVec 64 → Option (BitVec 512))
    (finishBlock : Option LiveBlock → BitVec 64 → Option LiveBlock → BitVec 64 → Option LiveBlock) :
    Prop where
  wellFormed : state.RefWF [sha]
  roundConstants : Sha512KHolds state sha kbits
  scalarReduce : ScalarReduceBy reduce
  shaInit : Sha512InitBy init
  shaAppend : Sha512AppendBy kbits append
  shaFinish : Sha512FiniBy kbits finish finishBlock
  baseTable : ∃ table,
    Firedancer.Ref.BaseTableHolds state table ∧
      BaseVals table _root_.Ed25519.basePoint _root_.Ed25519.wellFormed_basePoint

section

variable (msg : Pointer) (sz : BitVec 64) (sig pk sha : Pointer) (state : GlobalState)
  (args : VerifyArgs state msg sz sig pk sha)
  (reduce : BitVec 512 → Option (Fin 4 → BitVec 64)) (kbits : BitVec (80 * 64))
  (init : Option LiveBlock → BitVec 64 → Option (Option LiveBlock))
  (append : Option LiveBlock → BitVec 64 → List (BitVec 8) → Option (Option LiveBlock))
  (finish : Option LiveBlock → BitVec 64 → Option LiveBlock → BitVec 64 → Option (BitVec 512))
  (finishBlock : Option LiveBlock → BitVec 64 → Option LiveBlock → BitVec 64 → Option LiveBlock)
  (henv : FiredancerRefEnvironment state sha reduce kbits init append finish finishBlock)
  (hconforms : Firedancer.Ref.fd_ed25519_verify_spec msg sz sig pk sha state
    args.msgFits args.sigBuf args.sBuf args.pkBuf reduce kbits init append finish finishBlock)
  (digest : BitVec 512) (words : Fin 4 → BitVec 64)
  (hdigest : ed25519Digest init append finish (state.mem.live? sha.id) sha.offset
    (readBuf args.sigBuf) (readBuf args.pkBuf) (bytesOf (readWord args.msgFits)) = some digest)
  (hreduce : reduce digest = some words)

include henv hconforms hdigest hreduce

/-- A defined run and its exact policy characterization follow from the
existing verifier spec. The allocation/global frame and all non-SHA memory
are preserved as stated by that specification. -/
theorem firedancerRef_run_acceptance :
    ∃ (finalState : GlobalState) (ret : BitVec 32),
      firedancerRefRun msg sz sig pk sha state = .value ([.value ret]ₕ, finalState) ∧
      finalState.alloc = state.alloc ∧ finalState.globals = state.globals ∧
      (∀ block : BlockId, block ≠ sha.id → finalState.mem.live? block = state.mem.live? block) ∧
      (ret = FD_ED25519_SUCCESS ↔ FiredancerAccept
        (readBuf args.pkBuf) (readBuf args.sigBuf) (readBuf args.sBuf).toNat
        ((packWords words).toNat % 2 ^ 255)) := by
  obtain ⟨table, htable, hbase⟩ := henv.baseTable
  obtain ⟨finalState, ret, hrun, halloc, hglobals, hmemory, _, _, _, hs, ha, hr, hdecoded⟩ :=
    hconforms args.sigOff args.msgOff args.shaPtr args.shaOff henv.roundConstants
      args.shaSig args.shaPk args.shaMsg henv.wellFormed henv.scalarReduce
      henv.shaInit henv.shaAppend henv.shaFinish table htable hbase digest hdigest words hreduce
  refine ⟨finalState, ret, hrun, halloc, hglobals, hmemory, ?_⟩
  apply firedancer_success_iff_accept
  refine ⟨hs, ha, hr, ?_⟩
  intro hs A R hA hR
  obtain ⟨hAlo, hRlo, heq⟩ := hdecoded hs A R hA hR
  exact ⟨hAlo, hRlo, fun hnA hnR => (heq hnA hnR).1⟩

/-- Instantiate the clean execution obligation from the exact existing FD
specification at its legacy SHA bindings. This adapter explicitly retains the
three legacy SHA constants; it does not introduce any new assumptions. -/
theorem firedancerLegacy_executionRefines :
    FiredancerExecutionRefines
      ⟨Firedancer.Common.fd_sha512_init, Firedancer.Common.fd_sha512_append,
        Firedancer.Common.fd_sha512_fini⟩
      msg sz sig pk sha state (readBuf args.pkBuf) (readBuf args.sigBuf) (readBuf args.sBuf)
        ((packWords words).toNat % 2 ^ 255) := by
  obtain ⟨table, htable, hbase⟩ := henv.baseTable
  obtain ⟨finalState, ret, hrun, _, _, _, _, _, _, hs, ha, hr, hdecoded⟩ :=
    hconforms args.sigOff args.msgOff args.shaPtr args.shaOff henv.roundConstants
      args.shaSig args.shaPk args.shaMsg henv.wellFormed henv.scalarReduce
      henv.shaInit henv.shaAppend henv.shaFinish table htable hbase digest hdigest words hreduce
  refine ⟨finalState, ret, ?_, hs, ha, hr, ?_⟩
  · simpa only [firedancerRun, firedancerRefProgram_legacy] using hrun
  · intro hs A R hA hR
    obtain ⟨hAlo, hRlo, heq⟩ := hdecoded hs A R hA hR
    exact ⟨hAlo, hRlo, fun hnA hnR => (heq hnA hnR).1⟩

/-- Success of the actual SLLVM invocation is exactly the Firedancer acceptance
predicate at the scalar actually consumed. No SHA correctness is used. -/
theorem firedancerRef_observe_success_iff :
    firedancerRefObserve msg sz sig pk sha state = some FD_ED25519_SUCCESS ↔
      FiredancerAccept (readBuf args.pkBuf) (readBuf args.sigBuf) (readBuf args.sBuf).toNat
        ((packWords words).toNat % 2 ^ 255) := by
  obtain ⟨finalState, ret, hrun, _, _, _, haccept⟩ :=
    firedancerRef_run_acceptance msg sz sig pk sha state args reduce kbits init append
      finish finishBlock henv hconforms digest words hdigest hreduce
  simpa only [firedancerRefObserve, hrun, PoisonOr.value, Option.some.injEq] using haccept

/-- Cross-client acceptance policy at the scalar returned by Firedancer's
actual digest/reduction calls. Canonical R is the precise additional policy. -/
theorem agave_iff_firedancerRef_success_and_canonical :
    AgaveStrictAccept (readBuf args.pkBuf) (readBuf args.sigBuf) (readBuf args.sBuf).toNat
        ((packWords words).toNat % 2 ^ 255) ↔
      firedancerRefObserve msg sz sig pk sha state = some FD_ED25519_SUCCESS ∧
        CanonicalY (readBuf args.sigBuf) := by
  rw [firedancerRef_observe_success_iff msg sz sig pk sha state args reduce kbits init append
    finish finishBlock henv hconforms digest words hdigest hreduce]
  exact agave_iff_firedancer_and_canonical _ _ _ _

end

end Agave.Ed25519.Bridge

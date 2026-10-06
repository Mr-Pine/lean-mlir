import SSA.Projects.Agave.Ed25519.Bridge.FiredancerResult
import SSA.Projects.Firedancer.Ref.Mlir.fd_ed25519_verify

/-!
# The existing Firedancer region with explicit SHA programs

The legacy region binds its three SHA calls to signature-only constants.
Here those exact call sites are parameters. Every verifier block and every
other callee is preserved definitionally. The elaborator only unfolds the
verifier's generated block definitions and replaces those three references;
Lean checks the resulting term. There is no executable/verifier substitution.
-/

namespace Agave.Ed25519.Bridge

open LeanMLIR SLLVM Firedancer.Common

/-- The three external CFGs left abstract by the existing FD verifier lift. -/
structure FiredancerShaPrograms where
  init : Cfg (Ctxt.ofList [SLLVM.Ty.ptr]) [SLLVM.Ty.ptr]
  append : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr]
  finish : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr]

open Lean in
private meta def replaceVerifierSha (env : Environment) (init append finish : Expr) :
    Nat → Expr → Expr
  | 0, expression => expression
  | fuel + 1, expression => expression.replace fun term =>
      match term with
      | .const name levels =>
        if name == ``Firedancer.Common.fd_sha512_init then some init
        else if name == ``Firedancer.Common.fd_sha512_append then some append
        else if name == ``Firedancer.Common.fd_sha512_fini then some finish
        else if (``Firedancer.Ref.fd_ed25519_verify).isPrefixOf name then
          match env.find? name with
          | some (.defnInfo info) =>
            some (replaceVerifierSha env init append finish fuel
              (info.value.instantiateLevelParams info.levelParams levels))
          | _ => none
        else none
      | _ => none

open Lean Elab Term in
elab "firedancer_ref_sha% " init:term ", " append:term ", " finish:term : term => do
  let init ← Term.elabTerm init none
  let append ← Term.elabTerm append none
  let finish ← Term.elabTerm finish none
  let result := replaceVerifierSha (← getEnv) init append finish 32
    (mkConst ``Firedancer.Ref.fd_ed25519_verify)
  return result

/-- The exact existing FD reference CFG, with its three SHA callees supplied
as ordinary values instead of signature-only constants. -/
def firedancerRefProgram (sha : FiredancerShaPrograms) :
    Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr])
      [SLLVM.Ty.bitvec 32] :=
  firedancer_ref_sha% sha.init, sha.append, sha.finish

/-- The new program is definitionally the existing region at its legacy SHA
bindings. This theorem intentionally mentions the three legacy SHA constants;
the parameterized program and its clean observation theorems do not. -/
theorem firedancerRefProgram_legacy :
    firedancerRefProgram ⟨Firedancer.Common.fd_sha512_init,
      Firedancer.Common.fd_sha512_append, Firedancer.Common.fd_sha512_fini⟩ =
        Firedancer.Ref.fd_ed25519_verify := rfl

/-- Exact SLLVM execution, retaining all actual verifier and helper bodies. -/
noncomputable def firedancerRun (programs : FiredancerShaPrograms)
    (msg : Pointer) (sz : BitVec 64) (sig pk sha : Pointer) (state : GlobalState) :
    PoisonOr (HVector toType [SLLVM.Ty.bitvec 32] × GlobalState) :=
  StateT.run
    (runFunction ((firedancerRefProgram programs).denote
      (Ctxt.Valuation.ofHVector [.value sha, .value pk, .value sig, .value sz, .value msg]ₕ)))
    state

/-- Observe the raw return code, retaining undefined/poison execution as none. -/
noncomputable def firedancerObserve (programs : FiredancerShaPrograms)
    (msg : Pointer) (sz : BitVec 64) (sig pk sha : Pointer) (state : GlobalState) :
    Option (BitVec 32) :=
  match firedancerRun programs msg sz sig pk sha state with
  | .poison => none
  | .value (.cons .poison .nil, _) => none
  | .value (.cons (.value ret) .nil, _) => some ret

/-- The local execution obligation: termination plus the return-path checks
of the existing FD proof. It does not assume the acceptance equivalence that
will be derived, any hash correctness, or any canonical-encoding policy. -/
def FiredancerExecutionRefines (programs : FiredancerShaPrograms)
    (msg : Pointer) (sz : BitVec 64) (sig pk sha : Pointer) (state : GlobalState)
    (a r s : BitVec 256) (challenge : Nat) : Prop :=
  ∃ finalState ret,
    firedancerRun programs msg sz sig pk sha state = .value ([.value ret]ₕ, finalState) ∧
      FiredancerReturnChecks a r s.toNat challenge ret

attribute [local irreducible] firedancerRefProgram firedancerRun

/-- Only the standard logical foundations are needed: the SHA programs and
execution checks are explicit parameters and hypotheses. -/
theorem firedancerObserve_success_iff
    (programs : FiredancerShaPrograms) (msg : Pointer) (sz : BitVec 64)
    (sig pk sha : Pointer) (state : GlobalState) (a r s : BitVec 256) (challenge : Nat)
    (hexecution : FiredancerExecutionRefines programs msg sz sig pk sha state a r s challenge) :
    firedancerObserve programs msg sz sig pk sha state = some FD_ED25519_SUCCESS ↔
      FiredancerAccept a r s.toNat challenge := by
  obtain ⟨finalState, ret, hrun, hchecks⟩ := hexecution
  unfold firedancerObserve
  rw [hrun]
  change some ret = some FD_ED25519_SUCCESS ↔ _
  rw [Option.some.injEq]
  exact firedancer_success_iff_accept hchecks

/-- Clean policy-to-execution bridge for the actual FD CFG. The only execution
premise is the local termination/return-check contract; canonical R remains
an explicit policy difference. -/
theorem agave_iff_firedancerObserve_success_and_canonical
    (programs : FiredancerShaPrograms) (msg : Pointer) (sz : BitVec 64)
    (sig pk sha : Pointer) (state : GlobalState) (a r s : BitVec 256) (challenge : Nat)
    (hexecution : FiredancerExecutionRefines programs msg sz sig pk sha state a r s challenge) :
    AgaveStrictAccept a r s.toNat challenge ↔
      firedancerObserve programs msg sz sig pk sha state = some FD_ED25519_SUCCESS ∧
        CanonicalY r := by
  rw [firedancerObserve_success_iff programs msg sz sig pk sha state a r s challenge hexecution]
  exact agave_iff_firedancer_and_canonical a r s.toNat challenge

end Agave.Ed25519.Bridge

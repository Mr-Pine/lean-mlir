import SSA.Projects.Agave.Ed25519.Bridge.FiredancerProgram
import SSA.Projects.Firedancer.Ref.Proof.fd_ed25519_verify
import Lean.AddDecl

/-!
Replay the committed source proof with its three external SHA CFG constants
abstracted as ordinary program parameters. Only declarations transitively
depending on those constants are replayed; all arithmetic, curve, and memory
theorems are reused unchanged. Every generated declaration is submitted to
Lean's kernel with its transformed proof term. No execution equivalence or
SHA program identity is postulated.
-/

namespace Agave.Ed25519.Bridge

open Lean Meta Elab Command in
private meta partial def parameterizeFiredancerSha (name : Name) : MetaM Name := do
  let replayNamespace := `Agave.Ed25519.Bridge.ParameterizedSource
  let replacement := replayNamespace ++ name
  if (← getEnv).contains replacement then return replacement
  let targets : Array Name := #[
    ``Firedancer.Common.fd_sha512_init,
    ``Firedancer.Common.fd_sha512_append,
    ``Firedancer.Common.fd_sha512_fini]
  let info ← getConstInfo name
  let some value := info.value? true
    | throwError "Cannot replay SHA-dependent declaration {name}: no proof/body"
  for dependency in info.type.getUsedConstants ++ value.getUsedConstants do
    unless targets.contains dependency do
      if (← collectAxioms dependency).any targets.contains then
        discard <| parameterizeFiredancerSha dependency
  withLocalDeclD `programs (mkConst ``FiredancerShaPrograms) fun programs => do
    let env ← getEnv
    let transform (expression : Expr) : Expr := expression.replace fun term =>
      match term with
      | .const dependency levels =>
        if dependency == targets[0]! then some (mkProj ``FiredancerShaPrograms 0 programs)
        else if dependency == targets[1]! then some (mkProj ``FiredancerShaPrograms 1 programs)
        else if dependency == targets[2]! then some (mkProj ``FiredancerShaPrograms 2 programs)
        else if env.contains (replayNamespace ++ dependency) then
          some (mkApp (mkConst (replayNamespace ++ dependency) levels) programs)
        else none
      | _ => none
    let type ← mkForallFVars #[programs] (transform info.type)
    let value ← mkLambdaFVars #[programs] (transform value)
    match info with
    | .thmInfo _ =>
      addDecl <| .thmDecl {
        name := replacement
        levelParams := info.levelParams
        type := type
        value := value }
    | .defnInfo original =>
      addDecl <| .defnDecl {
        name := replacement
        levelParams := info.levelParams
        type := type
        value := value
        hints := original.hints
        safety := .safe }
    | _ => throwError "Unsupported SHA-dependent declaration kind: {name}"
    return replacement

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
set_option debug.skipKernelTC false in
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| parameterizeFiredancerSha ``Firedancer.Ref.fd_ed25519_verify_conforms

open LeanMLIR SLLVM Firedancer Firedancer.Common

/-- Call contracts for the supplied SHA CFGs, with the exact original
memory/termination footprints and no legacy program constants. -/
abbrev FiredancerShaInitBy := ParameterizedSource.Firedancer.Common.Sha512InitBy
abbrev FiredancerShaAppendBy := ParameterizedSource.Firedancer.Common.Sha512AppendBy
abbrev FiredancerShaFinishBy := ParameterizedSource.Firedancer.Common.Sha512FiniBy

theorem firedancerParameterizedProgram_eq (programs : FiredancerShaPrograms) :
    ParameterizedSource.Firedancer.Ref.fd_ed25519_verify programs =
      firedancerRefProgram programs := rfl

/-- The committed complete verifier conformance proof at arbitrary supplied
SHA programs. Its call contracts are the remaining program boundary. -/
theorem firedancerParameterizedSource_conforms (programs : FiredancerShaPrograms)
    (msg : Pointer) (sz : BitVec 64) (sig pk sha : Pointer)
    (state : GlobalState) (hmsg : Fits state.mem msg (sz.toNat * 8))
    (hr : IsByteBufPtr state.mem sig) (hS : IsByteBufPtr state.mem (sig.withOffset 32))
    (ha : IsByteBufPtr state.mem pk) (hsignull : sig.id ≠ nullBlock)
    (reduce : BitVec 512 → Option (Fin 4 → BitVec 64)) (kbits : BitVec (80 * 64))
    (init : Option LiveBlock → BitVec 64 → Option (Option LiveBlock))
    (append : Option LiveBlock → BitVec 64 → List (BitVec 8) → Option (Option LiveBlock))
    (finish : Option LiveBlock → BitVec 64 → Option LiveBlock → BitVec 64 → Option (BitVec 512))
    (finishBlock : Option LiveBlock → BitVec 64 → Option LiveBlock → BitVec 64 → Option LiveBlock) :
    ParameterizedSource.Firedancer.Ref.fd_ed25519_verify_spec programs
      msg sz sig pk sha state hmsg hr hS ha reduce kbits init append finish finishBlock :=
  ParameterizedSource.Firedancer.Ref.fd_ed25519_verify_conforms programs
    msg sz sig pk sha state hmsg hr hS ha hsignull reduce kbits init append finish finishBlock

end Agave.Ed25519.Bridge

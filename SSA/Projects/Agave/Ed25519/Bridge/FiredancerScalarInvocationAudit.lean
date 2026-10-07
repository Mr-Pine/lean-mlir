import SSA.Projects.Agave.Ed25519.Bridge.FiredancerScalarArithmeticAudit
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerScalarInvocation

/-! The optional invocation bridge is separate from the standard-foundation
source arithmetic manifest. Only its invocation-shaped endpoint retains the
three legacy SHA program constants. -/

/-- info: Firedancer reducer-choice adapters use only standard foundations; the invocation adapter retains exactly the three inventoried SHA program constants. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let foundations : List Name := [`propext, `Classical.choice, `Quot.sound]
  let targets : List Name := [
    ``Agave.Ed25519.Bridge.firedancerSourceReduce_packed,
    ``Agave.Ed25519.Bridge.firedancerSourceReduce_returns_of_certificate,
    ``Agave.Ed25519.Bridge.firedancerSourceReduce_value_of_certificate,
    ``Agave.Ed25519.Bridge.firedancerSourceReduce_valueCorrect_of_certificates]
  for target in targets do
    for dependency in (← collectAxioms target) do
      unless foundations.contains dependency do
        throwError "Uninventoried reducer-choice dependency of {target}: {dependency}"
  let legacy := foundations ++ [
    `Firedancer.Common.fd_sha512_init,
    `Firedancer.Common.fd_sha512_append,
    `Firedancer.Common.fd_sha512_fini]
  let actual := (← collectAxioms
    ``Agave.Ed25519.Bridge.FiredancerProofInvocation.challenge_eq_of_source_certificate).toList
  unless actual.length == legacy.length && legacy.all actual.contains do
    throwError "Unexpected invocation dependency inventory: {actual}"
  logInfo "Firedancer reducer-choice adapters use only standard foundations; the invocation adapter retains exactly the three inventoried SHA program constants."

import SSA.Projects.Agave.Ed25519.Bridge.CrossClientExistingProof

/-!
The original verifier proof and its cross-client adapter must have the same
small axiom boundary: Lean's three ordinary logical foundations and the three
explicit legacy SHA program constants. The imported arithmetic and memory
proofs use algebraic identities or bounded kernel reduction; native proof
certificates, admitted lemmas, and new semantic axioms are rejected here.
-/

/-- info: Existing FD proof and adapter retain exactly 3 standard foundations and 3 legacy SHA constants. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let expected : List Name := [
    `propext, `Classical.choice, `Quot.sound,
    `Firedancer.Common.fd_sha512_init,
    `Firedancer.Common.fd_sha512_append,
    `Firedancer.Common.fd_sha512_fini]
  let targets : List Name := [
    ``Firedancer.Ref.fd_ed25519_verify_conforms,
    ``Agave.Ed25519.Bridge.firedancerExistingProof_executionRefines,
    ``Agave.Ed25519.Bridge.existingProof_crossClient_observations]
  for target in targets do
    let mut actual : List Name := []
    for dependency in (← collectAxioms target) do
      actual := dependency :: actual
      unless expected.contains dependency do
        throwError "Uninventoried dependency of {target}: {dependency}"
    for dependency in expected do
      unless actual.contains dependency do
        throwError "Expected dependency missing from {target}: {dependency}"
    unless actual.length == expected.length do
      throwError "Expected {expected.length} dependencies for {target}, found {actual.length}"
  logInfo "Existing FD proof and adapter retain exactly 3 standard foundations and 3 legacy SHA constants."

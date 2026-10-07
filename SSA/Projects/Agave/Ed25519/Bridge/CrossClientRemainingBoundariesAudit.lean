import SSA.Projects.Agave.Ed25519.Bridge.CrossClientRemainingBoundaries

/-! Audit the composed witnesses themselves, including the canonical-R
specialization. Conditional implementation boundaries remain hypotheses;
the only axioms allowed are the three standard foundations and the original
Firedancer SHA program bindings. -/

/-- info: Composed cold endpoints retain exactly 3 standard foundations and 3 legacy SHA constants. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let expected : List Name := [
    `propext, `Classical.choice, `Quot.sound,
    `Firedancer.Common.fd_sha512_init,
    `Firedancer.Common.fd_sha512_append,
    `Firedancer.Common.fd_sha512_fini]
  let targets : List Name := [
    ``Agave.Ed25519.Bridge.provedLeaves_cold_crossClient_observations,
    ``Agave.Ed25519.Bridge.provedLeaves_cold_crossClient_of_canonical]
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
  logInfo "Composed cold endpoints retain exactly 3 standard foundations and 3 legacy SHA constants."

import SSA.Projects.Agave.Ed25519.Bridge.CrossClientExistingProofCold

/-! The existing Firedancer theorem supplies the FD run. Its three legacy SHA
bindings are explicit; no native certificate or additional semantic axiom is
accepted by this audit. Premises of the conditional theorem remain premises. -/

/-- info: Cold-cache existing-proof endpoint retains exactly 3 standard foundations and 3 legacy SHA constants. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let expected : List Name := [
    `propext, `Classical.choice, `Quot.sound,
    `Firedancer.Common.fd_sha512_init,
    `Firedancer.Common.fd_sha512_append,
    `Firedancer.Common.fd_sha512_fini]
  let target := ``Agave.Ed25519.Bridge.existingProof_cold_crossClient_observations
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
  logInfo "Cold-cache existing-proof endpoint retains exactly 3 standard foundations and 3 legacy SHA constants."

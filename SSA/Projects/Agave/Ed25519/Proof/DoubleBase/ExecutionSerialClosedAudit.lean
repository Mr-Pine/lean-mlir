import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialVerifier

/-- info: Closed serial backend and verifier callsite use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Tables.SerialConstructorContract.linked_contract,
    ``Agave.Ed25519.DoubleBase.RIR.serialLinked_doubleBaseContractUnder_closed,
    ``Agave.Ed25519.DoubleBase.RIR.serialLinked_dalek_call_closed,
    ``Agave.Ed25519.Verifier.Execution.Dalek.serial_block_verified,
    ``Agave.Ed25519.Verifier.Execution.Dalek.serial_tail_verified,
    ``Agave.Ed25519.Verifier.Execution.Dalek.serial_cold_context]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Closed serial backend and verifier callsite use only standard Lean axioms."

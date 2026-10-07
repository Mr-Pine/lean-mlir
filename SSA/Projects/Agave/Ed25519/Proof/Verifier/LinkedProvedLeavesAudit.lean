import SSA.Projects.Agave.Ed25519.Proof.Verifier.LinkedProvedLeaves

/-! The exact remaining premises are recorded in LinkedProvedLeaves:
* RemainingContracts contains CacheContract, serial/AVX2 DoubleBaseContract,
  and CompareContract (external bcmp).
* The linked decoder requires DecompressContractUnder Ready.
* The contextual endpoint requires Challenge.CompressContract; the cold/warm
  endpoint instead requires SHA512Finalization.CompressContractUnder.
* LinkedContextualLeaves.Inputs / LinkedColdLeaves.Inputs carry this invocation's
  constructor decoder call, successful output coordinates, memory, and globals.
No complete verifier execution or acceptance equality is among these premises.
The separate serial_doubleBase_contract_under has no table-execution premise;
its contextual contract still requires serialLinkedReady at the call state.
This audit checks foundations; it does not discharge the listed obligations.
-/

/-- info: Linked proved-leaf verifier composition uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.LinkedProvedLeaves.RemainingContracts.complete,
    ``Agave.Ed25519.Verifier.Execution.LinkedProvedLeaves.serial_doubleBase_contract_under,
    ``Agave.Ed25519.Verifier.Execution.LinkedProvedLeaves.primitive_calls_contextual,
    ``Agave.Ed25519.Verifier.Execution.LinkedProvedLeaves.observe_contextual,
    ``Agave.Ed25519.Verifier.Execution.LinkedProvedLeaves.primitive_calls_cold,
    ``Agave.Ed25519.Verifier.Execution.LinkedProvedLeaves.observe_cold]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Linked proved-leaf verifier composition uses only standard Lean axioms."

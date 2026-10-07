import SSA.Projects.Agave.Ed25519.Bridge.FiredancerScalarUniversal

/-! Exact closure audit for the universal source arithmetic result and its
readable-memory call adapter. Legacy SHA bindings are not in this slice. -/

/-- info: Universal Firedancer scalar reduction uses only propext, Classical.choice, and Quot.sound. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let foundations : List Name := [`propext, `Classical.choice, `Quot.sound]
  let targets : List Name := [
    ``Firedancer.Common.ScalarArithmetic.Registers.sourceReduce_eq,
    ``Firedancer.Common.ScalarArithmetic.IntegerRegisters.output_exact,
    ``Firedancer.Common.ScalarArithmetic.inputValue_eq,
    ``Firedancer.Common.ScalarArithmetic.Registers.reduce_eq_packingWords,
    ``Firedancer.Common.ScalarArithmetic.packed_output_value,
    ``Firedancer.Common.ScalarArithmetic.sourceReduce_correct,
    ``Agave.Ed25519.Bridge.firedancerScalarCanonical,
    ``Agave.Ed25519.Bridge.firedancerScalarReduce_run]
  for target in targets do
    for dependency in (← collectAxioms target) do
      unless foundations.contains dependency do
        throwError "Uninventoried universal scalar dependency of {target}: {dependency}"
  logInfo "Universal Firedancer scalar reduction uses only propext, Classical.choice, and Quot.sound."

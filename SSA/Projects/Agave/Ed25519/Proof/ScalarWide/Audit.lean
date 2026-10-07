import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Linked
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.CallPhases
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryProduct

/-! Guard the exact imports, extracted constants, and proved mathematical
adapters. This audit does not assert `ExecutionObligation`. -/

/-- info: Scalar-wide import and arithmetic endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.input_product_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.widened_mul_toNat,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.startup_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.startup_allocation_count,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.startup_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.startup_allocation_count,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.low_montgomery_call,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.high_montgomery_call,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.conditional_subtraction_black_box_call,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.conditional_subtraction_black_box_call,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.block_count,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.block_count,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.montgomeryR_value,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.montgomeryRR_value,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.radix_coprime,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.montgomery_quotient_bound,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.montgomery_quotient_mod,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.exact_of_split_reductions,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.reducedBytes_canonical,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.output_eq_reducedBytes,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.observations_of_contract,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.finalization_reduceWide]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Scalar-wide import and arithmetic endpoints use only standard Lean axioms."

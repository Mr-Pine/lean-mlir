import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.AddbackWords
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.UpperPacking
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Frame

/-! Audit of algebraic word refinements and exact local frame equations.
This audit does not assert the complete linked reducer's execution obligation. -/

/-- info: Scalar-wide word refinements use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction.borrowSteps_certificate,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction.differences_refine,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction.borrowSteps_addback,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction.addbackSums_bounds,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction.addbackSums_telescope,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction.addbackSums_mod,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction.borrow_addback_exact,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction.borrowByte_of_shift,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction.mask_add_three,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction.addback_refine,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction.conditional_subtract_words,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction.packed_conditional_subtract,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.productColumns_bound,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.cancellationSums_bounds,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.add128_flags,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.quotientLimbs_value,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.quotientLimbs_bounds,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.trunc128_mask52,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.final_carry_trunc,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.outputStores_erase,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.zeroizeStores_erase,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.stores_erase,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.startupState_erase,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.startupState_erase]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Scalar-wide word refinements use only standard Lean axioms."

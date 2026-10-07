import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryTail
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryCarry
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.ProductRefinement

/-! Flag and actual-machine cut-point audit. Every endpoint is a local
execution or word-expression theorem, not the unproved linked contract. -/

/-- info: Scalar-wide machine cut points use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.borrow_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.addback_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.tail_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.tailWords_value,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.masked52_shl44,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.carry_word_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.column1_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.column2_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.column3_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.column4_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.column5_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.column6_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.column7_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.column8_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.columnWords_mod,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.columnWords_toNat,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.columnWords_bound,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction.signed_add64,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction.addback_add64,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction.middle_borrow_flags,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction.high_bit_trunc_flags]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Scalar-wide machine cut points use only standard Lean axioms."

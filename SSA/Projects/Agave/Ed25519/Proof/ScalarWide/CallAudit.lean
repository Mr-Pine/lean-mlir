import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryCall
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputSplitArithmetic
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputChunk0
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputChunk1
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputChunk2
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputChunk3
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputChunk4
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputChunk5
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputChunk6
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputChunk7

/-! Audit the full Montgomery-call draft and outer-wrapper input cut points.
The wide-wrapper ExecutionObligation is still not asserted here. -/

/-- info: Scalar-wide call and input endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.carryWordEnv_quotient,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.wordCancellationSums_toNat,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.wordUpperSums_toNat,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.wordQuotientLimbs_toNat,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.actual_quotient_toNat,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.quotient52_widen,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.quotient52_value,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.montgomery_words_correct,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.productStates_read,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.productStates_erase,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.product_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.body_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.allocSteps_read,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.scratchPtrs_fits,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.startup_bodyReady,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.program_call,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.field_shl_nuw,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.field_shl_nsw_nuw,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.placedField_disjoint,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputChunk0_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputChunk1_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputChunk2_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputChunk3_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputChunk4_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputChunk5_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputChunk6_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputChunk7_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.lowSplitWords_extract,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.highSplitWords_extract,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.lowSplitWords_value,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.highSplitWords_value]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Scalar-wide call and input endpoints use only standard Lean axioms."

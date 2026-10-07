import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputRegisterBridge
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.SplitStores
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.FiveWordMemory
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.WrapperCalls
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.WrapperSum
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.WrapperSumArithmetic
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.WrapperSumRefinement
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.WrapperModularSum
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.WrapperBorrow
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.WrapperAddback
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.WrapperSubtract
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.ResultSlots
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputCleanup
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Serialization
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.ByteStores
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.FinalCleanup
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.ExactByteMemory
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.WrapperFrame

/-! Source-only wrapper phase audit. No full ExecutionObligation theorem is
asserted by this audit; passing requires all listed draft modules to elaborate. -/

/-- info: Scalar-wide wrapper phase endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputFragment_reg105,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputFragment_reg110,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputFragment_reg118,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputFragment_reg127,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputFragment_reg141,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputFragment_reg151,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputFragment_reg159,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputFragment_reg173,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputFragment_reg177,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputFragment_reg195,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputFragment_reg197,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputFragment_reg210,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputFragment_reg215,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputFragment_reg228,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputFragment_reg237,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputFragment_reg246,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputFragment_reg261,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.split_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.outputStores_smallRange,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.disjoint_word_slots,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.outputStores_read,
    ``Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.outputStores_read_other,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.copy40_read,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.low_copy_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.low_call_copy_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.high_copy_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.high_call_copy_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.montgomeryCopyState_range,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.montgomeryCopyState_count,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.montgomeryCopyState_read,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.sum_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.sumEnv_words,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.sumSums_bounds,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.sumSums_telescope,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.sumSums_value,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.sumWordSums_toNat,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.sumWords_toNat,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.sumWords_bound,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.sumWords_value,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.sum52_toNat,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.sum52_widen,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.sum52_value,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.wrapper_modular_sum,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.wrapper_borrow_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.wrapper_addback_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.wrapperAddbackEnv_words,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.wrapper_subtract_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.wrapperSubtractEnv_words,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.resultSlots_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.resultSlots_erase,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputCleanup_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.inputCleanup_erase,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.serialize_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.serializedBytes_packed,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.byteStores_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.finalCleanup_run,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.finalCleanup_erase,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.spliceBytePrefix_bit,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.spliceBytePrefix_full,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.storePrefix_block,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.storePrefix_other,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.storeBytes_exact,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.private_outputStores_erase,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.splitStores_erase,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.montgomeryCopyState_erase,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.storePrefix_erase,
    ``Agave.Ed25519.Verifier.Execution.ScalarWide.serialized_frame]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Scalar-wide wrapper phase endpoints use only standard Lean axioms."

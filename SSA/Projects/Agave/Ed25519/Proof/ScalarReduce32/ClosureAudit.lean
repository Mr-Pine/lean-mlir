import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Execution

/-! Kernel dependency audit for the unconditional concrete reducer endpoints. -/

/-- info: Scalar-reduce32 closure uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.ScalarReduce32.Execution.body_length,
    ``Agave.Ed25519.ScalarReduce32.Execution.body_decomposition,
    ``Agave.Ed25519.ScalarReduce32.Execution.startupScratch_local,
    ``Agave.Ed25519.ScalarReduce32.Execution.pipeline_memory,
    ``Agave.Ed25519.ScalarReduce32.Execution.pipeline_allocation_count,
    ``Agave.Ed25519.ScalarReduce32.Execution.reductionProducts_eq,
    ``Agave.Ed25519.ScalarReduce32.Execution.reductionProducts_bound,
    ``Agave.Ed25519.ScalarReduce32.Execution.reductionQuotient_widen,
    ``Agave.Ed25519.ScalarReduce32.Execution.montgomeryPhaseEnv_quotient,
    ``Agave.Ed25519.ScalarReduce32.Execution.reduction_carry_certificate,
    ``Agave.Ed25519.ScalarReduce32.Execution.reduction_finish_correct,
    ``Agave.Ed25519.ScalarReduce32.Execution.reductionWords_correct,
    ``Agave.Ed25519.ScalarReduce32.Execution.reductionBytes_packed,
    ``Agave.Ed25519.ScalarReduce32.Execution.reductionBytes_correct,
    ``Agave.Ed25519.ScalarReduce32.Execution.reductionData_ready,
    ``Agave.Ed25519.ScalarReduce32.Execution.pipeline_witnesses,
    ``Agave.Ed25519.ScalarReduce32.Execution.call,
    ``Agave.Ed25519.ScalarReduce32.Execution.contract]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Scalar-reduce32 closure uses only standard Lean axioms."

import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionAcceptance
import SSA.Projects.RIR.Tests.Syntax.MonotonicLoad

/-!
The instruction results concern the parsed monotonic byte load in sequential
RIR memory. The verifier results are conditional composition: the
`RefinesControlFlow`, global-state, primitive, bounded scalar arithmetic, and
compression premises remain visible. A standard axiom closure does not
discharge any of those execution contracts.
-/

/-- info: All eight verifier execution-interface endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``LeanMLIR.RIR.Instr.run_loadMonotonic,
    ``LeanMLIR.RIR.Tests.Syntax.MonotonicLoad.instruction_run_eq,
    ``Agave.Ed25519.Verifier.Execution.resultCode_is_ok,
    ``Agave.Ed25519.Verifier.Execution.final_comparison,
    ``Agave.Ed25519.Verifier.Execution.linked_observation_of_refinement,
    ``Agave.Ed25519.Verifier.Execution.observations_equal_of_refinement,
    ``Agave.Ed25519.Verifier.Execution.observe_true_iff_strict_accept,
    ``Agave.Ed25519.Verifier.Execution.observe_true_iff_firedancer_and_canonical]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All eight verifier execution-interface endpoints use only standard Lean axioms."

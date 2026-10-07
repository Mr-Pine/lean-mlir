import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarExecutionPrefix
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarExecutionRound

/-! Axiom audit for the exact dispatcher and scalar slices. The dispatcher
entry, cold initializer call site, warm AVX2 delegation and return, scalar
count-one CFG prefix, and first imported scalar round are covered. The
remaining 79 scalar rounds and full compression refinement are deliberately
not claimed by this audit. The AVX2 body is a separate development. -/

/-- info: Exact dispatcher and scalar SHA-512 slices use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.SHA512.Execution.Dispatch.dispatch_entry_body,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.dispatch_entry_step,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.dispatch_entry_runFrom,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.dispatch_entry_ready,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.dispatch_cold_step,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.dispatch_cold_runFrom,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.dispatch_return,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.dispatch_avx2_step,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.dispatch_avx2_runFrom,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.dispatch_warm_avx2,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.scalar_one_bounds_step,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.scalarChainState_eq_unpack,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.scalar_load_body,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.scalar_load_step,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.scalar_warm_one_steps,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.scalar_warm_one_runFrom,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.scalar_warm_one_evalFrom,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.scalar_one_cursor,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.scalar_choose_add,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.scalarFirstRound_eq,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.scalar_first_round_body,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.scalar_first_round_result,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.scalar_first_round_transition]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Exact dispatcher and scalar SHA-512 slices use only standard Lean axioms."

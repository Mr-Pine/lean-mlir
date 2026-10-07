import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarBulkFuel
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarBulkBackend

/-! Strict transitive standard-axiom audit of the arbitrary-count scalar source. -/

/-- info: Arbitrary-count scalar SHA-512 source execution uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.backend_before,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.backend_store,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.backend_cursor,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.scalar_bulk_runFrom,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.entry_constants,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.count_shift,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.count_gep,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.bounds_before,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.bounds_step,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.warm_scalar_bulk_run,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.warm_scalar_bulk_call,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.warm_scalar_bulk_call_ready,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.warm_scalar_bulk_contract,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.warm_scalar_bulk,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.warm_scalar_bulk_of_ready,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.scalar_loop_positive_eval,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.scalar_loop_positive,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.subrange,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.live_prefix,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.next_end,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.next_ne_end,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.run_readBytes_succ,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.warm_bounds_runFrom,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.warm_positive_runFrom,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.warm_zero_runFrom,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.before_trans,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.before_weaken,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.frame_before,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.constants_before,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.store_before,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.loop_before,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.loop_initial,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.loop_cursor,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.before_symm,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.load_before,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.body_before,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.one_body_before,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.body_constants,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.body_initial,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.body_store,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.body_cursor,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.scalar_body,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.continue_before,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.continue_body,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.scalar_continue,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.splice_read_self,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.store_read_self]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Arbitrary-count scalar SHA-512 source execution uses only standard Lean axioms."

#print axioms Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.warm_scalar_bulk_contract
#print axioms Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.scalar_bulk_runFrom
#print axioms Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk.scalar_loop_positive_eval

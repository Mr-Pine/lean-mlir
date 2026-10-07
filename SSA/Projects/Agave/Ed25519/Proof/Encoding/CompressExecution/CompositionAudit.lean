import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekCompressPrimitive

/-! Audit of the checked exact compressor body and conditional verifier adapter.
The individual lower invocation, frame, and field-value premises remain explicit.
The stronger concrete linked-call audit is `FullAudit`. -/

/-- info: Conditional compressor composition uses only the three standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Encoding.Compress.Execution.affine_prefix_run,
    ``Agave.Ed25519.Encoding.Compress.Execution.normalize_run,
    ``Agave.Ed25519.Encoding.Compress.Execution.normalizationSafety,
    ``Agave.Ed25519.Encoding.Compress.Execution.affine_tail_run,
    ``Agave.Ed25519.Encoding.Compress.Execution.program_run_of_calls,
    ``Agave.Ed25519.Encoding.Compress.Execution.program_call_of_calls,
    ``Agave.Ed25519.Encoding.Compress.Execution.FieldMemory.erase,
    ``Agave.Ed25519.Encoding.Compress.Execution.FieldMemory.affine_readback,
    ``Agave.Ed25519.Encoding.Compress.Execution.FieldValues.inverse_value,
    ``Agave.Ed25519.Encoding.Compress.Execution.FieldValues.affine_value,
    ``Agave.Ed25519.Encoding.Compress.Execution.encodedBytes_of_field_calls,
    ``Agave.Ed25519.Verifier.Execution.Dalek.compress_call_of_primitive_obligations,
    ``Agave.Ed25519.Verifier.Execution.Dalek.compressContract_of_primitive_obligations]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Conditional compressor composition uses only the three standard Lean axioms."

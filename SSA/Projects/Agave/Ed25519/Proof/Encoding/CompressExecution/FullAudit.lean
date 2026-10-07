import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekCompressPrimitive
import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Lower

/-! Audit of the exact-body composition and its conditional primitive adapter.
An axiom-clean conditional theorem does not discharge its explicit lower-call
premises. This file must pass before those endpoints are reported as checked. -/

/-- info: Compressor composition uses only the three standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Encoding.Compress.Execution.invertChain_eq_inverse,
    ``Agave.Ed25519.Encoding.Compress.Execution.affine_prefix_run,
    ``Agave.Ed25519.Encoding.Compress.Execution.normalize_run,
    ``Agave.Ed25519.Encoding.Compress.Execution.normalizationSafety,
    ``Agave.Ed25519.Encoding.Compress.Execution.program_call_of_calls,
    ``Agave.Ed25519.Encoding.Compress.Execution.FieldMemory.erase,
    ``Agave.Ed25519.Encoding.Compress.Execution.encodedBytes_of_field_calls,
    ``Agave.Ed25519.Encoding.Compress.Execution.linked_mul_call,
    ``Agave.Ed25519.Encoding.Compress.Execution.linked_pow2k5_call,
    ``Agave.Ed25519.Encoding.Compress.Execution.linked_blackBox_call,
    ``Agave.Ed25519.Verifier.Execution.Dalek.compress_call_of_primitive_obligations,
    ``Agave.Ed25519.Verifier.Execution.Dalek.compressContract_of_primitive_obligations]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Compressor composition uses only the three standard Lean axioms."

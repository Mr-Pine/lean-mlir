import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekCompressLinked

/-! Audit of the concrete imported compressor and its valid-point adapter.
Every arithmetic helper is linked to its checked RIR execution. The remaining
premises concern caller memory and the represented input point. -/

/-- info: Linked compressor and valid-point adapter use only the three standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Encoding.Decompress.Execution.storeLimbs_exact,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Pow22501.program_call,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Pow22501.program_call_field,
    ``Agave.Ed25519.Encoding.Compress.Execution.linked_mul_call,
    ``Agave.Ed25519.Encoding.Compress.Execution.linked_pow2k5_call,
    ``Agave.Ed25519.Encoding.Compress.Execution.linked_blackBox_call,
    ``Agave.Ed25519.Encoding.Compress.Execution.linked_pow22501_contract,
    ``Agave.Ed25519.Encoding.Compress.Execution.linked_primitive_obligations,
    ``Agave.Ed25519.Encoding.Compress.Execution.linked_compress_call,
    ``Agave.Ed25519.Verifier.Execution.Dalek.validPoint_compress_input_words,
    ``Agave.Ed25519.Verifier.Execution.Dalek.validPoint_compress_projective_input,
    ``Agave.Ed25519.Verifier.Execution.Dalek.validPoint_layout_compress_input_tight,
    ``Agave.Ed25519.Verifier.Execution.Dalek.validPoint_layout_compress_projective_input,
    ``Agave.Ed25519.Verifier.Execution.Dalek.compressContract_linked,
    ``Agave.Ed25519.Verifier.Execution.Dalek.linked_compress_contract]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Linked compressor and valid-point adapter use only the three standard Lean axioms."

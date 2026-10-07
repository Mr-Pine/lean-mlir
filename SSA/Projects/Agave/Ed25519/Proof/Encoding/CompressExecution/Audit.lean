import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Output
import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Linked

/-! Kernel dependency audit for the projective arithmetic and exact output
suffix. This does not claim that the full entry execution has been composed. -/

/-- info: Compressor output proofs use only the three standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Encoding.Compress.Execution.invertChain_eq_inverse,
    ``Agave.Ed25519.Encoding.Compress.Execution.serial_projective_compress,
    ``Agave.Ed25519.Encoding.Compress.Execution.store_projective_compress_run,
    ``Agave.Ed25519.Encoding.Compress.Execution.verifier_compression_is_imported]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Compressor output proofs use only the three standard Lean axioms."

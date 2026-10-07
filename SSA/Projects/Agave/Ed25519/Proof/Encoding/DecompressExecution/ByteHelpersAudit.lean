import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.ToBytes
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.BytesEq

/-- info: All 8 byte-helper endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Encoding.Decompress.Execution.ToBytes.program_call,
    ``Agave.Ed25519.Encoding.Decompress.Execution.ToBytes.program_correct,
    ``Agave.Ed25519.Encoding.Decompress.Execution.ToBytes.machine_canonical,
    ``Agave.Ed25519.Encoding.Decompress.Execution.ToBytes.storeBytes_readAt,
    ``Agave.Ed25519.Encoding.Decompress.Execution.ToBytes.storeBytes_read256,
    ``Agave.Ed25519.Encoding.Decompress.Execution.BytesEq.program_call,
    ``Agave.Ed25519.Encoding.Decompress.Execution.BytesEq.program_exact,
    ``Agave.Ed25519.Encoding.Decompress.Execution.BytesEq.comparison_exact]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All 8 byte-helper endpoints use only standard Lean axioms."

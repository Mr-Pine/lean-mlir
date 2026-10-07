import SSA.Projects.Agave.Ed25519.Proof.Verifier.BcmpByteABI

/-- info: All eleven bytewise bcmp ABI adapter endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.Dalek.Bcmp.ByteABI.input32_of_smallRange,
    ``Agave.Ed25519.Verifier.Execution.Dalek.Bcmp.ByteABI.read_byte,
    ``Agave.Ed25519.Verifier.Execution.Dalek.Bcmp.ByteABI.equal32_iff_readAt,
    ``Agave.Ed25519.Verifier.Execution.Dalek.Bcmp.ByteABI.invocation_iff,
    ``Agave.Ed25519.Verifier.Execution.Dalek.Bcmp.ByteABI.CallerFrame.readAt,
    ``Agave.Ed25519.Verifier.Execution.Dalek.Bcmp.ByteABI.CallerFrame.smallRange,
    ``Agave.Ed25519.Verifier.Execution.Dalek.Bcmp.ByteABI.CallerFrame.readBytes,
    ``Agave.Ed25519.Verifier.Execution.Dalek.Bcmp.ByteABI.FramedInvocation.toInvocation,
    ``Agave.Ed25519.Verifier.Execution.Dalek.Bcmp.ByteABI.compareContract_of_bytewise,
    ``Agave.Ed25519.Verifier.Execution.Dalek.Bcmp.ByteABI.compression_tail,
    ``Agave.Ed25519.Verifier.Execution.Dalek.Bcmp.ByteABI.compression_tail_framed]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All eleven bytewise bcmp ABI adapter endpoints use only standard Lean axioms."

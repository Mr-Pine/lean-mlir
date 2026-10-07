import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.AppendSemantic

/-! Strict transitive axiom closure of the concrete append observation proof. -/
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.result_represents
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.linked_call_represents

/-- info: Firedancer append observation refinement uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.readState_unpack,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.packed_readState,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.MemRep,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.MemRep.used,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.MemRep.observe,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.of_context,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.read_store_offsets,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.bytes_store_after,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.start_rep,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.chain_rep,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.writes_read,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.writes_bytes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.set_count_rep,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.bufferCopy,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.bufferCopy_chain,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.bufferCopy_bits,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.bufferCopy_bytes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.short_rep,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.aligned_nat,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.tail_rep,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.direct_rep,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.filledResult,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.filled_writes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.filled_rep,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.filled_suffix,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.filled_input_live,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.result_rep,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.result_represents,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.result_represents_exists,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.result_stream_represents,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic.linked_call_represents]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Firedancer append observation refinement uses only standard Lean axioms."

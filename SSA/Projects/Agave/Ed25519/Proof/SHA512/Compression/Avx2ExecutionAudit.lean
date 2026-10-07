import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionFeedForward

/-! Audit the concrete imported bb6 execution, its reachable exit after sixteen
steps, standard-round result, memory preservation, and register frame. This
covers the final-round loop and bb7 feed-forward; the preceding schedule loop
remains a separate execution obligation. -/

/-- info: Exact AVX2 SHA-512 tail and feed-forward use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.SHA512.Execution.Avx2.tailRound_eq,
    ``Agave.Ed25519.SHA512.Execution.Avx2.tail_body,
    ``Agave.Ed25519.SHA512.Execution.Avx2.tail_backedge,
    ``Agave.Ed25519.SHA512.Execution.Avx2.tail_exit,
    ``Agave.Ed25519.SHA512.Execution.Avx2.TailTrace.evalFrom,
    ``Agave.Ed25519.SHA512.Execution.Avx2.TailTrace.runFrom,
    ``Agave.Ed25519.SHA512.Execution.Avx2.tail_sixteen,
    ``Agave.Ed25519.SHA512.Execution.Avx2.tail_sixteen_runFrom,
    ``Agave.Ed25519.SHA512.Execution.Avx2.tail_sixteen_from_prefix,
    ``Agave.Ed25519.SHA512.Execution.Avx2.store_pair,
    ``Agave.Ed25519.SHA512.Execution.Avx2.feedForward_body,
    ``Agave.Ed25519.SHA512.Execution.Avx2.feedForward_block,
    ``Agave.Ed25519.SHA512.Execution.Avx2.feedForwardState_eq,
    ``Agave.Ed25519.SHA512.Execution.Avx2.feedForward_read_disjoint,
    ``Agave.Ed25519.SHA512.Execution.Avx2.tail_feedForward]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Exact AVX2 SHA-512 tail and feed-forward use only standard Lean axioms."

import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionTail

/-! Audit the concrete imported bb6 execution, its reachable exit after sixteen
steps, standard-round result, memory preservation, and register frame. This
covers the final-round slice; the preceding schedule loop and bb7 feed-forward
remain separate execution obligations. -/

/-- info: Exact AVX2 SHA-512 tail execution uses only standard Lean axioms. -/
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
    ``Agave.Ed25519.SHA512.Execution.Avx2.tail_sixteen_from_prefix]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Exact AVX2 SHA-512 tail execution uses only standard Lean axioms."

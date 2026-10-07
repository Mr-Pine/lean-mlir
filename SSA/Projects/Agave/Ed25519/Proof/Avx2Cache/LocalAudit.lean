import SSA.Projects.Agave.Ed25519.Proof.Avx2Cache.LocalContract

/-! Instruction observations remain explicit hypotheses. The audit checks the
proof of the actual imported CFG, not hardware semantics for those observations. -/

/-- info: All five local cache-instruction endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions.Local.initializer_run,
    ``Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions.Local.of_instructionContracts,
    ``Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions.Local.initializer_call,
    ``Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions.Local.initializer_call_framed,
    ``Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions.Local.cache_contract]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All five local cache-instruction endpoints use only standard Lean axioms."

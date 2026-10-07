import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorContract

/-! Transitive audit of the actual constructor and all composition boundaries. -/
open Lean in
run_cmd do
  for endpoint in [
      `Agave.Ed25519.Tables.Avx2Constructor.Entry.tight_run,
      `Agave.Ed25519.Tables.Avx2Constructor.CacheCombined.initial_run,
      `Agave.Ed25519.Tables.Avx2Constructor.CacheCombined.initial_point,
      `Agave.Ed25519.Tables.Avx2Constructor.CacheCombined.initial_frame,
      `Agave.Ed25519.Tables.Avx2Constructor.CacheCombined.successor_run,
      `Agave.Ed25519.Tables.Avx2Constructor.CacheCombined.successor_point,
      `Agave.Ed25519.Tables.Avx2Constructor.CacheCombined.successor_frame,
      `Agave.Ed25519.Tables.Avx2Constructor.PrefixState.frame,
      `Agave.Ed25519.Tables.Avx2Constructor.PrefixState.entries,
      `Agave.Ed25519.Tables.Avx2Constructor.StepState.frame,
      `Agave.Ed25519.Tables.Avx2Constructor.StepState.completed,
      `Agave.Ed25519.Tables.Avx2Constructor.Arithmetic.width5,
      `Agave.Ed25519.Tables.Avx2Constructor.Prefix.entry_run,
      `Agave.Ed25519.Tables.Avx2Constructor.Step.block_step,
      `Agave.Ed25519.Tables.Avx2Constructor.Loop.loop_run,
      `Agave.Ed25519.Tables.Avx2Constructor.Contract.contract,
      `Agave.Ed25519.Tables.Avx2Constructor.Contract.linked_contract,
      `Agave.Ed25519.Tables.Avx2Constructor.Contract.linked_helpers] do
    for dependency in (← collectAxioms endpoint) do
      unless [`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{endpoint} depends on forbidden axiom {dependency}"
    logInfo m!"standard-three audit passed: {endpoint}"

import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderSemantic

/-! Strict transitive foundation check. This establishes that the semantic
bridge uses only Lean's standard three axioms. It does not claim that the
explicit `PrefixBoundary` premise has been discharged from initialized globals.
-/

/-- info: All 11 decoder semantic endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Encoding.Decompress.sqrtRatio_success_iff_root,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.wordSqrt_value,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.wordStep1_value,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.pointWords_value,
    ``Agave.Ed25519.Encoding.Decompress.Valid.decoderCorrect,
    ``Agave.Ed25519.Encoding.Decompress.Valid.shared_correct,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.Semantic.linked_call_rejection,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.Semantic.linked_call_success,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.Semantic.linked_call_valid,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.Semantic.linked_call_classification,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.Semantic.contractUnder_of_prefixes]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All 11 decoder semantic endpoints use only standard Lean axioms."

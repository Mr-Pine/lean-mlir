import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressValidPointExecution

/-! The representation and decoder-correctness endpoints are unconditional.
`finishPoint_run` covers only the stated original suffix; the generic contract
adapter retains its actual-call hypothesis. This audit checks foundations and
does not discharge that missing full decoder execution premise. -/

/-- info: All 20 valid-point decompression endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Encoding.Decompress.Valid.coordinatePayload_eq,
    ``Agave.Ed25519.Encoding.Decompress.Valid.pointPayload_eq,
    ``Agave.Ed25519.Encoding.Decompress.Valid.words_bytes,
    ``Agave.Ed25519.Encoding.Decompress.Valid.pointWords_represents,
    ``Agave.Ed25519.Encoding.Decompress.Valid.decode_curve,
    ``Agave.Ed25519.Encoding.Decompress.Valid.decode_bytes,
    ``Agave.Ed25519.Encoding.Decompress.Valid.decoderCorrect,
    ``Agave.Ed25519.Encoding.Decompress.Valid.decode_eq_none_iff,
    ``Agave.Ed25519.Encoding.Decompress.Valid.decode_eq_some_iff,
    ``Agave.Ed25519.Encoding.Decompress.Valid.shared_correct,
    ``Agave.Ed25519.Encoding.Decompress.Valid.parsed_validY,
    ``Agave.Ed25519.Encoding.Decompress.Valid.ready_constant_words,
    ``Agave.Ed25519.Encoding.Decompress.Valid.finishPoint_allocation,
    ``Agave.Ed25519.Encoding.Decompress.Valid.finishPoint_present,
    ``Agave.Ed25519.Encoding.Decompress.Valid.rejection_allocation,
    ``Agave.Ed25519.Encoding.Decompress.Valid.rejection_present,
    ``Agave.Ed25519.Encoding.Decompress.Valid.finishPoint_run,
    ``Agave.Ed25519.Encoding.Decompress.Valid.finishPoint_observation,
    ``Agave.Ed25519.Encoding.Decompress.Valid.wordObservation_iff,
    ``Agave.Ed25519.Encoding.Decompress.Valid.contractUnder_of_word_execution]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All 20 valid-point decompression endpoints use only standard Lean axioms."

import SSA.Projects.Agave.Ed25519.Proof.Verifier.CanonicalScalar

/-! Guarded axiom audit of the bounded-scalar and represented acceptance
endpoints. Explicit execution and curve-semantic premises remain premises. -/

/-- info: Bounded scalar and represented acceptance endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.Dalek.reduceScalarBytes_eq_self_iff,
    ``Agave.Ed25519.Verifier.Execution.Dalek.scalarHighBitClear_of_canonical,
    ``Agave.Ed25519.Verifier.Execution.Dalek.scalarGate_iff_canonical,
    ``Agave.Ed25519.Verifier.Execution.Dalek.canonicalScalarParserContracts,
    ``Agave.Ed25519.Verifier.Execution.Dalek.scalarParseContract_no_alias,
    ``Agave.Ed25519.Verifier.verify_iff_strict_accept_represented,
    ``Agave.Ed25519.Verifier.verify_iff_firedancer_and_canonical_represented,
    ``Agave.Ed25519.Verifier.CanonicalScalar.encode_eq_iff,
    ``Agave.Ed25519.Verifier.CanonicalScalar.parse_eq_some_iff,
    ``Agave.Ed25519.Verifier.CanonicalScalar.parserContracts,
    ``Agave.Ed25519.Verifier.CanonicalScalar.representedSharedCorrect,
    ``Agave.Ed25519.Verifier.not_nat_ofNat_scalarParseContract]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Bounded scalar and represented acceptance endpoints use only standard Lean axioms."

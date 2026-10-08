import SSA.Projects.Agave.Ed25519.Bridge.FiredancerEnvironmentWitness

/-! Reject every nonstandard axiom in the raw field loader and simultaneous
Firedancer memory witness, including any transitive admitted or native-decide
axiom. Importing this module runs the audit. -/

/-- info: Firedancer raw constants and simultaneous environment use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerFieldInitializer.limb_bounds,
    ``Agave.Ed25519.Bridge.FiredancerFieldInitializer.decode_value,
    ``Agave.Ed25519.Bridge.FiredancerFieldInitializer.EntryLoaded.ptr,
    ``Agave.Ed25519.Bridge.FiredancerFieldInitializer.EntryLoaded.readLimb,
    ``Agave.Ed25519.Bridge.FiredancerFieldInitializer.EntryLoaded.fieldGlobal,
    ``Agave.Ed25519.Bridge.FiredancerFieldInitializer.Loaded.refWF,
    ``Agave.Ed25519.Bridge.FiredancerEnvironmentWitness.wf,
    ``Agave.Ed25519.Bridge.FiredancerEnvironmentWitness.fields,
    ``Agave.Ed25519.Bridge.FiredancerEnvironmentWitness.base,
    ``Agave.Ed25519.Bridge.FiredancerEnvironmentWitness.sha,
    ``Agave.Ed25519.Bridge.FiredancerEnvironmentWitness.reference,
    ``Agave.Ed25519.Bridge.FiredancerEnvironmentWitness.message_live,
    ``Agave.Ed25519.Bridge.FiredancerEnvironmentWitness.signature_live,
    ``Agave.Ed25519.Bridge.FiredancerEnvironmentWitness.publicKey_live,
    ``Agave.Ed25519.Bridge.FiredancerEnvironmentWitness.input,
    ``Agave.Ed25519.Bridge.FiredancerEnvironmentWitness.small,
    ``Agave.Ed25519.Bridge.FiredancerEnvironmentWitness.ready]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Firedancer raw constants and simultaneous environment use only standard Lean axioms."

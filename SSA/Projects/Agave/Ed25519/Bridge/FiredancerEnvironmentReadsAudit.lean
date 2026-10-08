import SSA.Projects.Agave.Ed25519.Bridge.FiredancerEnvironmentAudit
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerEnvironmentReads

/-- info: Firedancer initial and fresh-SHA caller reads use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerEnvironmentWitness.read_key,
    ``Agave.Ed25519.Bridge.FiredancerEnvironmentWitness.read_r,
    ``Agave.Ed25519.Bridge.FiredancerEnvironmentWitness.read_s,
    ``Agave.Ed25519.Bridge.FiredancerEnvironmentWitness.read_message,
    ``Agave.Ed25519.Bridge.FiredancerEnvironmentWitness.read_key_initial,
    ``Agave.Ed25519.Bridge.FiredancerEnvironmentWitness.read_signature_initial,
    ``Agave.Ed25519.Bridge.FiredancerEnvironmentWitness.read_message_initial,
    ``Agave.Ed25519.Bridge.FiredancerEnvironmentWitness.bytes_packMessage,
    ``Agave.Ed25519.Bridge.FiredancerEnvironmentWitness.read_message_list,
    ``Agave.Ed25519.Bridge.FiredancerEnvironmentWitness.read_r_split,
    ``Agave.Ed25519.Bridge.FiredancerEnvironmentWitness.read_s_split]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Firedancer initial and fresh-SHA caller reads use only standard Lean axioms."

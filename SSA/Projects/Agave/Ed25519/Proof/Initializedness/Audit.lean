import SSA.Projects.Agave.Ed25519.Proof.Initializedness.ShadowTrace
import SSA.Projects.Agave.Ed25519.Proof.Initializedness.FiredancerRing

/-- info: Initializedness cutpoints and abstract byte-trace noninterference use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Initializedness.full_overwrite_read_eq,
    ``Agave.Ed25519.Initializedness.challenge_tail_copy,
    ``Agave.Ed25519.Initializedness.challenge_first_copy,
    ``Agave.Ed25519.Initializedness.challenge_second_copy,
    ``Agave.Ed25519.Initializedness.challenge_tail_not_written,
    ``Agave.Ed25519.Initializedness.padding_ignores_unused_bytes,
    ``Agave.Ed25519.Initializedness.ShadowTrace.step_agrees,
    ``Agave.Ed25519.Initializedness.ShadowTrace.observation_agrees,
    ``Agave.Ed25519.Initializedness.ShadowTrace.defined_trace_observations_equal,
    ``Agave.Ed25519.Initializedness.FiredancerRing.rounds_ignore_initial_ring]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Initializedness cutpoints and abstract byte-trace noninterference use only standard Lean axioms."

import SSA.Projects.Agave.Ed25519.Bridge.FiredancerBaseTableLoader

/-! Strict transitive axiom audit for the concrete Firedancer initializer. -/

/-- info: All 128 Firedancer base-table entries and their global loader use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerBaseInitializer.limb_bounds,
    ``Agave.Ed25519.Bridge.FiredancerBaseInitializer.cache_correct,
    ``Agave.Ed25519.Bridge.FiredancerBaseInitializer.point_zero,
    ``Agave.Ed25519.Bridge.FiredancerBaseInitializer.advance_certificate,
    ``Agave.Ed25519.Bridge.FiredancerBaseInitializer.point_represents,
    ``Agave.Ed25519.Bridge.FiredancerBaseInitializer.cache_eq_mathematical,
    ``Agave.Ed25519.Bridge.FiredancerBaseInitializer.Loaded.pointPtr,
    ``Agave.Ed25519.Bridge.FiredancerBaseInitializer.Loaded.readLimb_exact,
    ``Agave.Ed25519.Bridge.FiredancerBaseInitializer.Loaded.limbBounds,
    ``Agave.Ed25519.Bridge.FiredancerBaseInitializer.Loaded.readPoint,
    ``Agave.Ed25519.Bridge.FiredancerBaseInitializer.Loaded.baseTableHolds,
    ``Agave.Ed25519.Bridge.FiredancerBaseInitializer.initialize_loaded,
    ``Agave.Ed25519.Bridge.FiredancerBaseInitializer.initialize_baseTableHolds,
    ``Agave.Ed25519.Bridge.FiredancerBaseInitializer.initialize_wf,
    ``Agave.Ed25519.Bridge.FiredancerBaseInitializer.globalsReady_of_loaded]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All 128 Firedancer base-table entries and their global loader use only standard Lean axioms."

#print axioms Agave.Ed25519.Bridge.FiredancerBaseInitializer.cache_eq_mathematical
#print axioms Agave.Ed25519.Bridge.FiredancerBaseInitializer.Loaded.baseTableHolds
#print axioms Agave.Ed25519.Bridge.FiredancerBaseInitializer.initialize_baseTableHolds
#print axioms Agave.Ed25519.Bridge.FiredancerBaseInitializer.globalsReady_of_loaded

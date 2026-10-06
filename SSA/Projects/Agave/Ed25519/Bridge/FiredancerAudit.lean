import SSA.Projects.Agave.Ed25519.Bridge.FiredancerFullInput
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerExecution

/-! Guard the clean endpoint separately from the explicitly legacy adapter. -/

/-- info: 'Agave.Ed25519.Bridge.firedancer_success_iff_accept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Bridge.firedancer_success_iff_accept

/-- info: 'Agave.Ed25519.Bridge.firedancerRefProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Bridge.firedancerRefProgram

/-- info: 'Agave.Ed25519.Bridge.firedancerObserve_success_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Bridge.firedancerObserve_success_iff

/--
info: 'Agave.Ed25519.Bridge.agave_iff_firedancerObserve_success_and_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Agave.Ed25519.Bridge.agave_iff_firedancerObserve_success_and_canonical

/--
info: 'Agave.Ed25519.Bridge.agaveFull_iff_firedancerObserve_success_and_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Agave.Ed25519.Bridge.agaveFull_iff_firedancerObserve_success_and_canonical

/--
info: 'Agave.Ed25519.Bridge.firedancerLegacy_executionRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Firedancer.Common.fd_sha512_append,
 Firedancer.Common.fd_sha512_fini,
 Firedancer.Common.fd_sha512_init]
-/
#guard_msgs in
#print axioms Agave.Ed25519.Bridge.firedancerLegacy_executionRefines

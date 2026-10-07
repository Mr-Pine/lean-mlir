import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.Refinement
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.Word

/-! Guards on the checked arithmetic and scalar-instruction endpoints.
The exact observation execution endpoints have a separate audit. -/

/-- info: 'Agave.Ed25519.Avx2PointAdd.add_reduced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.add_reduced

/-- info: 'Agave.Ed25519.Avx2PointAdd.sub_reduced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.sub_reduced

/-- info: 'Agave.Ed25519.Avx2PointAdd.add_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.add_refines

/-- info: 'Agave.Ed25519.Avx2PointAdd.sub_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.sub_refines

/-- info: 'Agave.Ed25519.Avx2PointAdd.add_refines_serial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.add_refines_serial

/-- info: 'Agave.Ed25519.Avx2PointAdd.rir_lazyNeg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.rir_lazyNeg

/-- info: 'Agave.Ed25519.Avx2PointAdd.rir_lazyDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.rir_lazyDiff

/-- info: 'Agave.Ed25519.Avx2PointAdd.rir_lazySum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.rir_lazySum

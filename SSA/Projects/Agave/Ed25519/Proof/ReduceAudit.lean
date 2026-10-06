import SSA.Projects.Agave.Ed25519.Proof.ReduceBitcast
import SSA.Projects.Agave.Ed25519.Proof.ReduceProgram
import SSA.Projects.Agave.Ed25519.Proof.ReduceArithmetic

/-- info: 'Agave.Ed25519.bitcast_split32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.bitcast_split32

/-- info: 'Agave.Ed25519.bitcast_join64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.bitcast_join64

/-- info: 'Agave.Ed25519.split32_join64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.split32_join64

/-- info: 'Agave.Ed25519.Field.reduce_integer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Field.reduce_integer

/-- info: 'Agave.Ed25519.Field.reduce_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Field.reduce_residue

/-- info: 'Agave.Ed25519.Field.reduce_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Field.reduce_bounds

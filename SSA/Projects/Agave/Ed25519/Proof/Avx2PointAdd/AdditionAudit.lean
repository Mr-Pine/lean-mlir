import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.AdditionBridge
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.AdditionCallerFrame

/-! The exact backend addition interface and concrete caller frame are checked
with Lean's standard extensionality, choice and quotient laws only. -/

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.addition22_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.addition22_post

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.addition25_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.addition25_post

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.addition29_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.addition29_post

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.addition33_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.addition33_post

/--
info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.additionBlocks_of_imported_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.additionBlocks_of_imported_mul

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.CallerFrame.pointAdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.CallerFrame.pointAdd

/--
info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.pipelineState_callerFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.pipelineState_callerFrame

/--
info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.BackendReady.of_pointAddFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.BackendReady.of_pointAddFrame

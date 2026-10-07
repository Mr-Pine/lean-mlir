import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Concrete

/-! Strict axiom audit of the inhabited concrete backend, including its actual
prefix producer, every local input, concrete helper linkage and Dalek frame. -/

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.LoopRegisters.addConstants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.LoopRegisters.addConstants

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.LoopRegisters.doubleConstants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.LoopRegisters.doubleConstants

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.liveContext_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.liveContext_stable

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.LiveContext.of_privateFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.LiveContext.of_privateFrame

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.prefix_liveContext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.prefix_liveContext

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.loopScratch_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.loopScratch_memory

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.liveArithmeticInputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.liveArithmeticInputs

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.liveArithmeticBlocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.liveArithmeticBlocks

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.concrete_backend_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.concrete_backend_refines

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.concrete_doubleBaseContractUnder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.concrete_doubleBaseContractUnder

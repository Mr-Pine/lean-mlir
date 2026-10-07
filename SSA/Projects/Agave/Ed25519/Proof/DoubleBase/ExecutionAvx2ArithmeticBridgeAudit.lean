import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2ArithmeticBridge

/-! The integration remains conditional on square and table contracts, with
ordinary live-in/cache/frame inputs. No additional axioms are introduced. -/

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.arithmeticBlocks_of_local_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.arithmeticBlocks_of_local_inputs

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.framedArithmeticBlocks_of_local_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.framedArithmeticBlocks_of_local_inputs

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.doubleBaseContractUnder_of_imported_arithmetic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.doubleBaseContractUnder_of_imported_arithmetic

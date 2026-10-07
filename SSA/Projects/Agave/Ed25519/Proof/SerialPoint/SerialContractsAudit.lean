import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.SerialContractsLink

/-! Guard the exact lifted doubling execution and its CFG contract adapter. -/

/-- info: 'Agave.Ed25519.SerialPoint.Execution.double_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.SerialPoint.Execution.double_call

/-- info: 'Agave.Ed25519.SerialPoint.Execution.double_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.SerialPoint.Execution.double_readback

/-- info: 'Agave.Ed25519.SerialPoint.Execution.double_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.SerialPoint.Execution.double_contract

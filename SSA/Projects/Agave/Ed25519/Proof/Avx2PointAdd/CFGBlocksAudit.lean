import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGBlocks

/-! Guarded axiom audit for the complete local execution endpoints. These
guards are deliberately checked only after every dependency has compiled.
Expected axioms are Lean's standard extensionality, choice and quotient laws;
any additional axiom or admitted proof causes the guard to fail. -/

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.block22_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.block22_endpoint

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.block22_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.block22_run

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.block25_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.block25_endpoint

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.block25_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.block25_run

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.block29_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.block29_endpoint

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.block29_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.block29_run

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.block33_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.block33_endpoint

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.block33_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.block33_run

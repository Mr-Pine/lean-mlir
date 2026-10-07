import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.AdditionBaseCache

/-! Strict audits of actual static-global bounds, byte decoding, readback and
preservation. Every exported endpoint uses only the standard three laws. -/

/--
info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.baseCachePoint_reduced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.baseCachePoint_reduced

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.baseCachePoint_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.baseCachePoint_value

/--
info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.baseGlobal_readBlocks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.baseGlobal_readBlocks

/--
info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.baseGlobal_pointReduced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.baseGlobal_pointReduced

/--
info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.baseGlobal_pointValue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.baseGlobal_pointValue

/--
info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.baseCache_of_globalsReady' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.baseCache_of_globalsReady

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.BaseCache.row_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.BaseCache.row_live

/--
info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.BaseCache.row_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.BaseCache.row_correct

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.BaseCache.of_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.BaseCache.of_reads

/--
info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.BaseCache.of_pointAddFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.BaseCache.of_pointAddFrame

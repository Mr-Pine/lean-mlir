import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCacheScaleFrame

/-! Guarded axiom audit for the exact constructor scale/reduce instruction bridge. -/

/-- info: 'Agave.Ed25519.Tables.Avx2Constructor.CacheScale.initialScale_slice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Tables.Avx2Constructor.CacheScale.initialScale_slice

/-- info: 'Agave.Ed25519.Tables.Avx2Constructor.CacheScale.successorScale_slice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Tables.Avx2Constructor.CacheScale.successorScale_slice

/-- info: 'Agave.Ed25519.Tables.Avx2Constructor.CacheScale.initial_point' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Tables.Avx2Constructor.CacheScale.initial_point

/-- info: 'Agave.Ed25519.Tables.Avx2Constructor.CacheScale.successor_point' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Tables.Avx2Constructor.CacheScale.successor_point

/-- info: 'Agave.Ed25519.Tables.Avx2Constructor.CacheScale.scaledPoint_reduced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Tables.Avx2Constructor.CacheScale.scaledPoint_reduced

/-- info: 'Agave.Ed25519.Tables.Avx2Constructor.CacheScale.initial_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Tables.Avx2Constructor.CacheScale.initial_frame

/-- info: 'Agave.Ed25519.Tables.Avx2Constructor.CacheScale.successor_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Tables.Avx2Constructor.CacheScale.successor_frame

/-- info: 'Agave.Ed25519.Tables.Avx2Constructor.CacheScale.ConstantsReady.of_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Tables.Avx2Constructor.CacheScale.ConstantsReady.of_frame

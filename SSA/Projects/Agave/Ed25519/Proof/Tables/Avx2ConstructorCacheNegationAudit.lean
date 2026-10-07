import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCacheNegationFrame

/-! Guarded audit of the exact D-coordinate negation and its state frame. -/

/-- info: 'Agave.Ed25519.Tables.Avx2Constructor.CacheNegation.instructions_point' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Tables.Avx2Constructor.CacheNegation.instructions_point

/-- info: 'Agave.Ed25519.Tables.Avx2Constructor.CacheNegation.initial_slice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Tables.Avx2Constructor.CacheNegation.initial_slice

/-- info: 'Agave.Ed25519.Tables.Avx2Constructor.CacheNegation.successor_slice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Tables.Avx2Constructor.CacheNegation.successor_slice

/-- info: 'Agave.Ed25519.Tables.Avx2Constructor.CacheNegation.initial_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Tables.Avx2Constructor.CacheNegation.initial_correct

/-- info: 'Agave.Ed25519.Tables.Avx2Constructor.CacheNegation.successor_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Tables.Avx2Constructor.CacheNegation.successor_correct

/-- info: 'Agave.Ed25519.Tables.Avx2Constructor.CacheNegation.initial_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Tables.Avx2Constructor.CacheNegation.initial_frame

/-- info: 'Agave.Ed25519.Tables.Avx2Constructor.CacheNegation.successor_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Tables.Avx2Constructor.CacheNegation.successor_frame

/-- info: 'Agave.Ed25519.Tables.Avx2Constructor.CacheNegation.ConstantsReady.of_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Tables.Avx2Constructor.CacheNegation.ConstantsReady.of_frame

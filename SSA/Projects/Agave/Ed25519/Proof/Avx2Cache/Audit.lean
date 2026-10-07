import SSA.Projects.Agave.Ed25519.Proof.Avx2Cache.Contract

/-! Audit of the instruction-conditional imported execution proof. These axiom
lists do not discharge the explicit `InstructionContracts` hypotheses. -/

/-- info: 'Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions.xgetbv_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions.xgetbv_call

/-- info: 'Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions.initializer_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions.initializer_run

/-- info: 'Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions.initializer_call_of_instructions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions.initializer_call_of_instructions

/-- info: 'Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions.cache_store_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions.cache_store_execution

/-- info: 'Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions.cache_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions.cache_contract

/-- info: 'Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions.cache_call_normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions.cache_call_normalized

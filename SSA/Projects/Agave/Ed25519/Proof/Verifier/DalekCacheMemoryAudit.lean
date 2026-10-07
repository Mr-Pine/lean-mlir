import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekCacheMemory

/-! Audit the conditional memory adapter; this does not discharge its explicit
`CacheStoreExecution` parameter or prove execution of hardware instructions. -/

/-- info: 'Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.stored_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.stored_frame
/-- info: 'Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.stored_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.stored_read
/-- info: 'Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.contract_of_store_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.contract_of_store_execution

import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekCacheObservation

/-! Cache independence endpoints; hardware execution remains explicit. -/

/-- info: 'Agave.Ed25519.Conformance.pure_cache_all_messages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Conformance.pure_cache_all_messages

/-- info: 'Agave.Ed25519.Verifier.Execution.Dalek.backend_tail_of_selected_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Verifier.Execution.Dalek.backend_tail_of_selected_contract

/-- info: 'Agave.Ed25519.Verifier.Execution.Dalek.dispatch_tail_of_selected_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Verifier.Execution.Dalek.dispatch_tail_of_selected_contract

/-- info: 'Agave.Ed25519.Verifier.Execution.Dalek.initialized_tail_of_local_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Verifier.Execution.Dalek.initialized_tail_of_local_execution

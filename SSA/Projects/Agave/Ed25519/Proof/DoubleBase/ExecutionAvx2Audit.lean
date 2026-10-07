import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Backend
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2MulContracts

/-! Kernel-audited endpoints that do not depend on the square helper.
The final backend endpoints retain their explicit local arithmetic premises. -/

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.imported_mul_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.imported_mul_contract

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.avx2_entry_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.avx2_entry_run

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.avx2_naf5_loop_sourceDigits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.avx2_naf5_loop_sourceDigits

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.avx2_naf8_loop_sourceDigits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.avx2_naf8_loop_sourceDigits

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.prefix_to_ladder_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.prefix_to_ladder_run

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.ladder_run_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.ladder_run_represents

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.unpack_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.unpack_run

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.unpackStore_readPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.unpackStore_readPoint

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.outputBlock_of_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.outputBlock_of_ready

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.prefix_backendReady' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.prefix_backendReady

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.backend_refines_of_local_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.backend_refines_of_local_blocks

/-- info: 'Agave.Ed25519.DoubleBase.ExecutionAvx2.backend_refines_of_arithmetic_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Agave.Ed25519.DoubleBase.ExecutionAvx2.backend_refines_of_arithmetic_blocks

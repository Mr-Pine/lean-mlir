import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseMultiplication
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2ContractDefs

/-! The point-local helper contract is the shared caller contract without an
unrelated square-refinement import. The actual helper and packed state facts
are checked independently of the enclosing CFG-block composition. -/
namespace Agave.Ed25519.Avx2PointAdd.Execution
open LeanMLIR.RIR

theorem mulContract_iff_shared
    (call : Vals [.ptr, .ptr, .ptr] → EffectM (Vals [])) :
    MulContract call ↔ DoubleBase.ExecutionAvx2.MulContract call := Iff.rfl

end Agave.Ed25519.Avx2PointAdd.Execution

/-- info: 'Agave.Ed25519.Avx2PointAdd.Execution.imported_mul_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.Execution.imported_mul_contract

/-- info: 'Agave.Ed25519.Avx2PointAdd.Execution.multiply_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.Execution.multiply_call

/-- info: 'Agave.Ed25519.Avx2PointAdd.Phases.multiply_packed_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.Phases.multiply_packed_state

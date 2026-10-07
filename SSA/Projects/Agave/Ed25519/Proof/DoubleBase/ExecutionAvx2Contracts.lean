import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2MulContracts
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2SquareContracts

/-! Combined public helper boundary for the imported AVX2 double-base program.
The pure definitions and multiplication proof can be checked independently
of the square helper. No contract assumes a double-base loop result. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2

open LeanMLIR.RIR PointArithmetic
open Reduce64.Execution (SmallRange storeOutputs outputWord)
open Conformance.BackendExecution (Invocation readPoint)

/-- Link the two field helpers to their proved imported bodies. The table and
panic effects are kept separately named, exactly as at the source boundary. -/
noncomputable def linkedArithmetic
    (table : Vals [.ptr, .ptr] → EffectM (Vals []))
    (panic : Vals [.bv 64, .bv 64, .ptr] → EffectM (Vals [])) : Avx2CFG.Primitives where
  call0 := table
  call1 := Avx2SquareNegateD.Execution.program.call
  call2 := Avx2FieldMul.program.call
  call3 := panic

theorem linkedArithmetic_contracts
    (table : Vals [.ptr, .ptr] → EffectM (Vals []))
    (panic : Vals [.bv 64, .bv 64, .ptr] → EffectM (Vals []))
    (htable : TableContract table) : HelperContracts (linkedArithmetic table panic) :=
  ⟨htable, imported_square_contract, imported_mul_contract⟩


end Agave.Ed25519.DoubleBase.ExecutionAvx2

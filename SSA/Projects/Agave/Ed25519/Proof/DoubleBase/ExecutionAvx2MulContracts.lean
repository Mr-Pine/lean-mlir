import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2ContractDefs
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionRefinement

/-! Bind the raw multiplication contract to the checked imported helper. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2

open LeanMLIR.RIR PointArithmetic
open Reduce64.Execution (SmallRange storeOutputs outputWord)
open Conformance.BackendExecution (Invocation readPoint)

theorem imported_mul_contract : MulContract Avx2FieldMul.program.call := by
  intro r a b s hwf hr ha hb
  exact Avx2FieldMul.Execution.kernel_call_words r a b s hwf hr ha hb

/-- A helper satisfying the raw multiplication contract inherits the checked
integer-product readback for all four lanes under the asymmetric caller bound.
This is a consequence of its local contract, not an additional assumption. -/
theorem mul_product_of_contract
    (call : Vals [.ptr, .ptr, .ptr] → EffectM (Vals [])) (hcall : MulContract call)
    (r a b : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 160) (ha : SmallRange s.mem a 160)
    (hb : SmallRange s.mem b 160)
    (hleft : ∀ lane, Avx2FieldMul.LeftBound
      (Avx2FieldMul.Execution.inputNat (Avx2FieldMul.Execution.readBlocks s.mem a) lane))
    (hright : ∀ lane, Avx2FieldMul.RightBound
      (Avx2FieldMul.Execution.inputNat (Avx2FieldMul.Execution.readBlocks s.mem b) lane)) :
    ∃ s' : GlobalState,
      call (args3 r a b) s = .value (.nil, s') ∧
      ∀ (lane : Fin 4) (limb : Fin 10),
        (outputWord s'.mem r limb lane).toNat =
          Avx2FieldMul.product
            (Avx2FieldMul.Execution.inputNat (Avx2FieldMul.Execution.readBlocks s.mem a) lane)
            (Avx2FieldMul.Execution.inputNat (Avx2FieldMul.Execution.readBlocks s.mem b) lane)
            limb := by
  obtain ⟨s', hprogram, hwords, _⟩ :=
    Avx2FieldMul.Execution.kernel_correct r a b s hwf hr ha hb hleft hright
  refine ⟨s', ?_, hwords⟩
  exact (hcall r a b s hwf hr ha hb).trans
    ((Avx2FieldMul.Execution.kernel_call_words r a b s hwf hr ha hb).symm.trans hprogram)


end Agave.Ed25519.DoubleBase.ExecutionAvx2

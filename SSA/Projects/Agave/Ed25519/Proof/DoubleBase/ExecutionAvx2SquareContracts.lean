import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2ContractDefs
import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionRefinement

/-! Bind the square/negative-square contract to the checked imported helper. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2

open LeanMLIR.RIR PointArithmetic
open Reduce64.Execution (SmallRange storeOutputs outputWord)
open Conformance.BackendExecution (Invocation readPoint)

theorem imported_square_contract :
    SquareContract Avx2SquareNegateD.Execution.program.call := by
  intro r a s hwf hr ha
  exact Avx2SquareNegateD.Execution.kernel_call_words r a s hwf hr ha

/-- The local square contract yields the actual reduced output limbs, including
the negated D lane, under the checked point-doubling input bound. -/
theorem square_output_of_contract
    (call : Vals [.ptr, .ptr] → EffectM (Vals [])) (hcall : SquareContract call)
    (r a : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 160) (ha : SmallRange s.mem a 160)
    (hinput : ∀ lane, Avx2SquareNegateD.Bounded
      (Avx2SquareNegateD.Execution.inputNat
        (Avx2SquareNegateD.Execution.readBlocks s.mem a) lane)) :
    ∃ s' : GlobalState,
      call (args2 r a) s = .value (.nil, s') ∧
      ∀ (lane : Fin 4) (limb : Fin 10),
        (outputWord s'.mem r limb lane).toNat =
          Avx2SquareNegateD.output
            (Avx2SquareNegateD.Execution.inputNat
              (Avx2SquareNegateD.Execution.readBlocks s.mem a) lane)
            (decide (lane = 3)) limb := by
  obtain ⟨s', hprogram, hwords, _⟩ :=
    Avx2SquareNegateD.Execution.kernel_correct r a s hwf hr ha hinput
  refine ⟨s', ?_, hwords⟩
  exact (hcall r a s hwf hr ha).trans
    ((Avx2SquareNegateD.Execution.kernel_call_words r a s hwf hr ha).symm.trans hprogram)


end Agave.Ed25519.DoubleBase.ExecutionAvx2

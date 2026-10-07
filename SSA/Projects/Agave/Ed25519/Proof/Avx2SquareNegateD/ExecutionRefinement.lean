import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionKernel
import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionPacking
import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionArithmetic

namespace Agave.Ed25519.Avx2SquareNegateD.Execution
open LeanMLIR.RIR
open Reduce64.Execution

/-- Exact execution with the square, D subtraction, and carry word model exposed. -/
theorem kernel_call_words (r a : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 160) (ha : SmallRange s.mem a 160) :
    program.call (program.args (.value r) (.value a)) s =
      .value (.nil, {s with mem := storeOutputs s.mem r (signedColumns4 (readBlocks s.mem a))}) := by
  rw [kernel_call r a s hwf hr ha, wordTrace_eq_packedOutput]
  rfl

/-- Full execution and readback for the actual five-store square kernel.
The input bound is the one obtained from X,Y,Z,X+Y in point doubling. -/
theorem kernel_correct (r a : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 160) (ha : SmallRange s.mem a 160)
    (hinput : ∀ lane, Bounded (inputNat (readBlocks s.mem a) lane)) :
    ∃ s' : GlobalState,
      program.call (program.args (.value r) (.value a)) s = .value (.nil, s') ∧
      (∀ (lane : Fin 4) (limb : Fin 10),
        (outputWord s'.mem r limb lane).toNat =
          output (inputNat (readBlocks s.mem a) lane) (decide (lane = 3)) limb) ∧
      (∀ lane : Fin 4,
        if lane = 3 then
          (decode (fun limb => (outputWord s'.mem r limb lane).toNat) +
            decode (inputNat (readBlocks s.mem a) lane)^2) % modulus = 0
        else
          decode (fun limb => (outputWord s'.mem r limb lane).toNat) % modulus =
            decode (inputNat (readBlocks s.mem a) lane)^2 % modulus) := by
  refine ⟨{s with mem := storeOutputs s.mem r (signedColumns4 (readBlocks s.mem a))},
    kernel_call_words r a s hwf hr ha, ?_, ?_⟩
  · intro lane limb
    exact outputWord_square _ _ _ hr lane (hinput lane) limb
  · intro lane
    simp only [outputWord_square _ _ _ hr lane (hinput lane)]
    by_cases hd : lane = 3
    · simp only [hd, ↓reduceIte, decide_true]
      exact negative_square_result (hinput 3)
    · simp only [hd, ↓reduceIte, decide_false]
      exact square_result _

end Agave.Ed25519.Avx2SquareNegateD.Execution

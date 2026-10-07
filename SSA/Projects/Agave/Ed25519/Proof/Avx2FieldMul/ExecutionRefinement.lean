import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionKernel
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionPacking
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionArithmetic

namespace Agave.Ed25519.Avx2FieldMul.Execution
open LeanMLIR.RIR
open Reduce64.Execution

/-- Exact execution with the convolution and carry word model exposed. -/
theorem kernel_call_words (r a b : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 160) (ha : SmallRange s.mem a 160)
    (hb : SmallRange s.mem b 160) :
    program.call (program.args (.value r) (.value a) (.value b)) s =
      .value (.nil, {s with mem := storeOutputs s.mem r (rawColumns4 (readBlocks s.mem a) (readBlocks s.mem b))}) := by
  rw [kernel_call r a b s hwf hr ha hb, wordTrace_eq_packedOutput]
  rfl

/-- The full compiler-kernel endpoint. This theorem states execution, actual
memory readback, and field multiplication for all four physical SIMD lanes. -/
theorem kernel_correct (r a b : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 160) (ha : SmallRange s.mem a 160)
    (hb : SmallRange s.mem b 160)
    (hleft : ∀ lane, LeftBound (inputNat (readBlocks s.mem a) lane))
    (hright : ∀ lane, RightBound (inputNat (readBlocks s.mem b) lane)) :
    ∃ s' : GlobalState,
      program.call (program.args (.value r) (.value a) (.value b)) s = .value (.nil, s') ∧
      (∀ (lane : Fin 4) (limb : Fin 10),
        (outputWord s'.mem r limb lane).toNat =
          product (inputNat (readBlocks s.mem a) lane)
            (inputNat (readBlocks s.mem b) lane) limb) ∧
      (∀ lane : Fin 4,
        Field.decode10 (fun limb => (outputWord s'.mem r limb lane).toNat) % Field.p =
          (Field.decode10 (inputNat (readBlocks s.mem a) lane) *
            Field.decode10 (inputNat (readBlocks s.mem b) lane)) % Field.p) := by
  refine ⟨{s with mem := storeOutputs s.mem r (rawColumns4 (readBlocks s.mem a) (readBlocks s.mem b))},
    kernel_call_words r a b s hwf hr ha hb, ?_, ?_⟩
  · intro lane limb
    exact outputWord_product _ _ _ _ hr lane (hleft lane) (hright lane) limb
  · intro lane
    simp only [outputWord_product _ _ _ _ hr lane (hleft lane) (hright lane)]
    exact product_mod _ _

end Agave.Ed25519.Avx2FieldMul.Execution

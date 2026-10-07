import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixNumerator

/-! Opaque instruction arithmetic lemmas prevent the kernel from repeatedly
normalizing the carry guards inside larger register-environment equalities. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
open LeanMLIR.RIR
set_option maxRecDepth 16000

theorem carry_operation (x y : BitVec 64) :
    Operation.add {nsw := true, nuw := true}
      (.value (x &&& 2251799813685247#64)) (.value (y >>> 51)) =
      .value ((x &&& 2251799813685247#64) + (y >>> 51)) := by
  have hu := (SerialPoint.weak_carry_add_nooverflow x y).1
  have hs := (SerialPoint.weak_carry_add_nooverflow x y).2
  simp only [Operation.add, PoisonOr.value_bind, hs, hu, Bool.false_eq_true,
    and_false, ite_false, PoisonOr.pure_def]

theorem carry_vector_operation (x y z w : BitVec 64) :
    BinOp.compute (BinOp.vector (BinOp.add {nsw := true, nuw := true}))
      (Ty.wrap #v[x &&& 2251799813685247#64, z &&& 2251799813685247#64])
      (Ty.wrap #v[y >>> 51, w >>> 51]) =
      Ty.wrap #v[(x &&& 2251799813685247#64) + (y >>> 51),
        (z &&& 2251799813685247#64) + (w >>> 51)] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [BinOp.compute, Ty.wrap, carry_operation]

theorem fold_operation (x y : BitVec 64) :
    Operation.add {nsw := true, nuw := true}
      (.value ((x >>> 51) * 19#64)) (.value (y &&& 2251799813685247#64)) =
      .value ((x >>> 51) * 19#64 + (y &&& 2251799813685247#64)) := by
  have hu : ((x >>> 51) * 19#64).uaddOverflow (y &&& 2251799813685247#64) = false :=
    (SerialPoint.weak_fold_nooverflow x y).1
  have hs : ((x >>> 51) * 19#64).saddOverflow (y &&& 2251799813685247#64) = false :=
    (SerialPoint.weak_fold_nooverflow x y).2
  simp only [Operation.add, PoisonOr.value_bind, hs, hu, Bool.false_eq_true,
    and_false, ite_false, PoisonOr.pure_def]

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix

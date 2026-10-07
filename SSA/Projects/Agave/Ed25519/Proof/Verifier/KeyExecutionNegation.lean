import SSA.Projects.Agave.Ed25519.Proof.Verifier.KeyExecutionSuccess
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.Word

/-! The constructor's actual inline word expressions implement field negation.
The input bound is only needed for this mathematical interpretation, not to
execute the emitted wrapping subtraction and bounded carry instructions. -/
namespace Agave.Ed25519.Verifier.Execution.Key
open SerialFieldMul

theorem negResult_weakWord (x : Words) : negResult x = SerialPoint.weakWord (negWord x) := by
  funext i
  fin_cases i <;> simp [negResult, SerialPoint.weakWord, add_comm]

theorem negWord_unsigned (x : Words) (hx : Bounded (unsigned x)) :
    unsigned (negWord x) = SerialPoint.biasedSub (fun _ => 0) (unsigned x) := by
  funext i
  have hb := SerialPoint.bias_large i
  have hx' := hx i
  have hconst : (if i = 0 then (36028797018963664 : BitVec 64) else 36028797018963952).toNat =
      SerialPoint.bias i := by fin_cases i <;> decide
  simp only [unsigned, negWord]
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; rw [hconst]; exact Nat.le_trans (Nat.le_of_lt hx') hb)]
  rw [hconst]
  simp [SerialPoint.biasedSub, unsigned]

theorem negResult_unsigned (x : Words) (hx : Bounded (unsigned x)) :
    unsigned (negResult x) = SerialPoint.sub (fun _ => 0) (unsigned x) := by
  rw [negResult_weakWord, SerialPoint.weakWord_unsigned, negWord_unsigned x hx]
  rfl

/-- X and T are negated in the field; Y and Z are unchanged by the emitted copies. -/
theorem negResult_value (x : Words) (hx : Bounded (unsigned x)) :
    SerialPoint.value (unsigned (negResult x)) = -SerialPoint.value (unsigned x) := by
  rw [negResult_unsigned x hx, SerialPoint.sub_value _ _ hx]
  simp [SerialPoint.value, SerialFieldMul.decode]

theorem negResult_tight (x : Words) : SerialPoint.Tight (unsigned (negResult x)) := by
  rw [negResult_weakWord, SerialPoint.weakWord_unsigned]
  exact SerialPoint.weakReduce_tight _ (fun i => (negWord x i).isLt)

end Agave.Ed25519.Verifier.Execution.Key

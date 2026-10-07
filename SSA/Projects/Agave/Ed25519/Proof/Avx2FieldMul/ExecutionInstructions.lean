import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.Instructions
import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.Unpack
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.ScalarSafety
import SSA.Projects.RIR.Run.Tactic
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionSimpAttrs

/-! Total scalar instruction rules for the extracted AVX2 field kernels.
The rules retain LLVM's flags.  Their proofs use only the widths of the
original words, so the execution theorem does not assume arithmetic bounds.
The separate arithmetic refinement supplies the point-caller limb bounds. -/

namespace Agave.Ed25519.Avx2FieldMul.Execution
open LeanMLIR.RIR
open Avx2SquareNegateD

theorem add_value (x y : BitVec w) :
    Operation.add {} (.value x) (.value y) = .value (x + y) := by
  simp [Operation.add]

theorem mul_value (x y : BitVec w) :
    Operation.mul {} (.value x) (.value y) = .value (x * y) := by
  simp [Operation.mul]

/-- The AVX2 low-word mask is a truncation followed by zero extension. -/
theorem mask32_eq_wide (x : BitVec 64) :
    x &&& 4294967295#64 = (x.setWidth 32).setWidth 64 := by
  have h := BitVec.and_setWidth_allOnes 32 32 x
  change x &&& 4294967295#64 = 0#32 ++ x.setWidth 32 at h
  exact h.trans (zero_append_eq_wide _)

theorem carry_mask26_value (x y : BitVec 64) :
    Operation.add {nsw := true, nuw := true}
      (.value (x >>> 25)) (.value (y &&& 67108863#64)) =
      .value ((x >>> 25) + (y &&& 67108863#64)) := by
  simp [Operation.add, (Reduce64.carry_mask26_flags x y).1,
    (Reduce64.carry_mask26_flags x y).2]

theorem carry_mask25_value (x y : BitVec 64) :
    Operation.add {nsw := true, nuw := true}
      (.value (x >>> 26)) (.value (y &&& 33554431#64)) =
      .value ((x >>> 26) + (y &&& 33554431#64)) := by
  simp [Operation.add, (Reduce64.carry_mask25_flags x y).1,
    (Reduce64.carry_mask25_flags x y).2]

theorem low_mul19_value (x : BitVec 64) :
    Operation.mul {nsw := true, nuw := true}
      (.value ((x >>> 25) &&& 67108863#64)) (.value 19#64) =
      .value (((x >>> 25) &&& 67108863#64) * 19#64) := by
  simp [Operation.mul, (Reduce64.low_mul19_flags x).1,
    (Reduce64.low_mul19_flags x).2]

theorem high_mul19_value (x : BitVec 64) :
    Operation.mul {nsw := true, nuw := true}
      (.value (x >>> 51)) (.value 19#64) =
      .value ((x >>> 51) * 19#64) := by
  simp [Operation.mul, (Reduce64.high_mul19_flags x).1,
    (Reduce64.high_mul19_flags x).2]

theorem low_fold_value (x y : BitVec 64) :
    Operation.add {nsw := true, nuw := true}
      (.value (((x >>> 25) &&& 67108863#64) * 19#64))
      (.value (y &&& 67108863#64)) =
      .value ((((x >>> 25) &&& 67108863#64) * 19#64) +
        (y &&& 67108863#64)) := by
  simp [Operation.add, (Reduce64.low_fold_flags x y).1,
    (Reduce64.low_fold_flags x y).2]

theorem high_fold_value (x y : BitVec 64) :
    Operation.add {nsw := true, nuw := true}
      (.value ((x >>> 51) * 19#64)) (.value (y &&& 33554431#64)) =
      .value (((x >>> 51) * 19#64) + (y &&& 33554431#64)) := by
  simp [Operation.add, (Reduce64.high_fold_flags x y).1,
    (Reduce64.high_fold_flags x y).2]

theorem final_carry_value (x y z : BitVec 64) :
    Operation.add {nsw := true, nuw := true}
      (.value (((x >>> 51) * 19#64) + (y &&& 33554431#64)))
      (.value (z >>> 26)) =
      .value ((((x >>> 51) * 19#64) + (y &&& 33554431#64)) +
        (z >>> 26)) := by
  simp [Operation.add, (Reduce64.final_carry_flags x y z).1,
    (Reduce64.final_carry_flags x y z).2]

attribute [avx2_execution_simp] bitcast_split32 bitcast_join64
  split32 join64 zero_append_eq_wide mask32_eq_wide add_value mul_value
  mul_wide_value mul19_wide_value carry_mask26_value carry_mask25_value
  low_mul19_value high_mul19_value low_fold_value high_fold_value final_carry_value

end Agave.Ed25519.Avx2FieldMul.Execution

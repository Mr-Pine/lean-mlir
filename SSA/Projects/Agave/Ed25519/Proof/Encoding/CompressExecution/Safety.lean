import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Inline

/-! Scalar poison obligations of the inline serializers. The Y carries reuse
the standalone serializer's checked bounds; X uses the same quotient carries
but adds q instead of 19q because only the resulting parity is consumed. -/
namespace Agave.Ed25519.Encoding.Compress.Execution
open LeanMLIR.RIR
open Encoding.RIR
open Decompress.Execution.ToBytes

private theorem sadd_comm (a b : BitVec 64) :
    a.saddOverflow b = b.saddOverflow a := by
  simp [BitVec.saddOverflow, Int.add_comm]

private theorem uadd_comm (a b : BitVec 64) :
    a.uaddOverflow b = b.uaddOverflow a := by
  simp [BitVec.uaddOverflow, Nat.add_comm]

/-- The compressor's parity shortcut needs only a one-bit quotient. -/
theorem parity_add_safe (x : Field.Serial) :
    (quotientWord x).saddOverflow (weakWord x 0) = false ∧
    (quotientWord x).uaddOverflow (weakWord x 0) = false := by
  have hq : (quotientWord x).toNat ≤ 1 := by
    rw [quotientWord_toNat]
    exact quotient_weakReduce_le_one _ (fun i => (x i).isLt)
  exact add_safe_of_bound _ _ 1 (radix + 19 * 2^13) hq
    (Nat.le_of_lt (weakWord_bound x 0)) (by norm_num [radix])

private theorem add_run {a b : BitVec 64}
    (hs : a.saddOverflow b = false) (hu : a.uaddOverflow b = false) :
    Operation.add {nsw := true, nuw := true} (.value a) (.value b) = .value (a + b) := by
  simp [Operation.add, hs, hu]

private theorem mul_run {a b : BitVec 64}
    (hs : a.smulOverflow b = false) (hu : a.umulOverflow b = false) :
    Operation.mul {nsw := true, nuw := true} (.value a) (.value b) = .value (a * b) := by
  simp [Operation.mul, hs, hu]

attribute [-simp] BitVec.shiftLeft_add_distrib in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem normalizationSafety (x y : Field.Serial) : NormalizationSafety x y := by
  have hy := toBytesSafe3 (y 0) (y 1) (y 2) (y 3) (y 4)
  have hx := toBytesSafe3 (x 0) (x 1) (x 2) (x 3) (x 4)
  dsimp only at hy hx
  rcases hy with ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11,
    y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23,
    y24, y25, y26, y27, y28, y29, y30, y31, y32, y33, _, _, _, _, _, _, _, _⟩
  rcases hx with ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11,
    x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, _⟩
  obtain ⟨xlastS, xlastU⟩ := parity_add_safe x
  dsimp only [quotientWord, carriedWord, weakWord] at xlastS xlastU
  dsimp only [NormalizationSafety]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_run y0 y1
  · exact add_run y2 y3
  · exact add_run y4 y5
  · exact add_run y6 y7
  · exact add_run y8 y9
  · exact add_run y10 y11
  · exact add_run y12 y13
  · exact add_run y14 y15
  · exact add_run y16 y17
  · exact add_run y18 y19
  · exact add_run y20 y21
  · exact mul_run y22 y23
  · exact add_run y24 y25
  · exact add_run y26 y27
  · exact add_run y28 y29
  · exact add_run y30 y31
  · exact add_run y32 y33
  · simp [Operation.shl, masked_shift_3_signed, masked_shift_3_unsigned]
  · simp [Operation.or, boundary_disjoint_3]
  · simp [Operation.shl, masked_shift_6_signed, masked_shift_6_unsigned]
  · simp [Operation.or, boundary_disjoint_6]
  · simp [Operation.shl, masked_shift_1_signed, masked_shift_1_unsigned]
  · simp [Operation.or, boundary_disjoint_1]
  · simp [Operation.shl, masked_shift_4_signed, masked_shift_4_unsigned]
  · simp [Operation.or, boundary_disjoint_4]
  · simp [Operation.trunc, last_byte_trunc_unsigned, last_byte_trunc_signed]
  · exact mul_run x0 x1
  · exact add_run x2 x3
  · exact add_run x4 x5
  · exact add_run x6 x7
  · exact add_run x8 x9
  · exact add_run x10 x11
  · exact add_run x12 x13
  · apply add_run
    · simpa only [BitVec.add_comm, sadd_comm] using x14
    · simpa only [BitVec.add_comm, uadd_comm] using x15
  · apply add_run
    · simpa only [BitVec.add_comm, sadd_comm] using x16
    · simpa only [BitVec.add_comm, uadd_comm] using x17
  · apply add_run
    · simpa only [BitVec.add_comm, sadd_comm] using x18
    · simpa only [BitVec.add_comm, uadd_comm] using x19
  · apply add_run
    · simpa only [BitVec.add_comm, sadd_comm] using x20
    · simpa only [BitVec.add_comm, uadd_comm] using x21
  · apply add_run
    · simpa only [BitVec.add_comm, sadd_comm, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val_zero', Matrix.cons_val_succ',
        BitVec.ofNat_eq_ofNat, Nat.cast_ofNat] using xlastS
    · simpa only [BitVec.add_comm, uadd_comm, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val_zero', Matrix.cons_val_succ',
        BitVec.ofNat_eq_ofNat, Nat.cast_ofNat] using xlastU

end Agave.Ed25519.Encoding.Compress.Execution

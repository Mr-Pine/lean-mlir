import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline956Model
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtWords
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixOperations

/-! The exact final sqrt-ratio inline tail. The only incoming facts concern
registers, live memory and the two candidate limb arrays at pc956. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline956
open LeanMLIR.RIR SerialFieldMul SerialPoint.Execution
open Reduce64.Execution (SmallRange)
open Decode.InlinePrefix (vector_two carry_operation carry_vector_operation fold_operation)
set_option maxRecDepth 32000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] v751 v753 v755 v776 v777 v763 v764 v765 v784 v785 v788

theorem small_add (a b : BitVec 64) (ha : a.toNat < 2^60) (hb : b.toNat < 2^60) :
    Operation.add {nsw := true, nuw := true} (.value a) (.value b) = .value (a + b) := by
  have ai : a.toInt = (a.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have bi : b.toInt = (b.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hu : a.uaddOverflow b = false := by
    simp only [BitVec.uaddOverflow, decide_eq_false_iff_not]; omega
  have hs : a.saddOverflow b = false := by
    simp only [BitVec.saddOverflow, ai, bi, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    constructor <;> omega
  simp [Operation.add, hs, hu]

theorem safe761 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    Operation.add {nsw := true, nuw := true}
      (.value ((v759 r t b x y))) (.value ((v754 r t b x y))) = .value (v761 r t b x y) := by
  simp [v754, v759, v761, BinOp.compute, vector_two, mlir_operation,
    SerialPoint.weak_mul_nooverflow, SerialPoint.weak_fold_nooverflow, SerialPoint.weak_carry_add_nooverflow]

theorem safe762 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    Operation.add {nsw := true, nuw := true}
      (.value ((v760 r t b x y))) (.value ((v756 r t b x y))) = .value (v762 r t b x y) := by
  simp [v756, v760, v762, BinOp.compute, vector_two, mlir_operation,
    SerialPoint.weak_mul_nooverflow, SerialPoint.weak_fold_nooverflow, SerialPoint.weak_carry_add_nooverflow]

theorem safe769 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    BinOp.compute (BinOp.vector (BinOp.add {nsw := true, nuw := true}))
      (Ty.wrap (v768 r t b x y)) (Ty.wrap (v766 r t b x y)) = Ty.wrap (v769 r t b x y) := by
  simp [v766, v768, v769, BinOp.compute, vector_two, mlir_operation,
    SerialPoint.weak_mul_nooverflow, SerialPoint.weak_fold_nooverflow, SerialPoint.weak_carry_add_nooverflow]

theorem safe782 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    Operation.mul {nsw := true, nuw := true}
      (.value ((v779 r t b x y))) (.value (19#64)) = .value (v782 r t b x y) := by
  simp [v779, v782, BinOp.compute, vector_two, mlir_operation,
    SerialPoint.weak_mul_nooverflow, SerialPoint.weak_fold_nooverflow, SerialPoint.weak_carry_add_nooverflow]

theorem safe783 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    Operation.add {nsw := true, nuw := true}
      (.value ((v781 r t b x y))) (.value ((v778 r t b x y))) = .value (v783 r t b x y) := by
  simp [v778, v781, v783, BinOp.compute, vector_two, mlir_operation,
    SerialPoint.weak_mul_nooverflow, SerialPoint.weak_fold_nooverflow, SerialPoint.weak_carry_add_nooverflow]

theorem safe790 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    Operation.mul {nsw := true, nuw := true}
      (.value ((v786 r t b x y))) (.value (19#64)) = .value (v790 r t b x y) := by
  simp [v786, v790, BinOp.compute, vector_two, mlir_operation,
    SerialPoint.weak_mul_nooverflow, SerialPoint.weak_fold_nooverflow, SerialPoint.weak_carry_add_nooverflow]

theorem safe791 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    Operation.add {nsw := true, nuw := true}
      (.value ((v782 r t b x y))) (.value ((v758 r t b x y))) = .value (v791 r t b x y) := by
  simpa only [v758, v779, v782, v791] using fold_operation (v776 r t b x y) (v751 r t b x y)

theorem safe792 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    Operation.add {nsw := true, nuw := true}
      (.value ((v780 r t b x y))) (.value ((v757 r t b x y))) = .value (v792 r t b x y) := by
  simp [v757, v780, v792, BinOp.compute, vector_two, mlir_operation,
    SerialPoint.weak_mul_nooverflow, SerialPoint.weak_fold_nooverflow, SerialPoint.weak_carry_add_nooverflow]

theorem safe793 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    Operation.add {nsw := true, nuw := true}
      (.value ((v791 r t b x y))) (.value (19#64)) = .value (v793 r t b x y) := by
  have h := RIR.toBytesSafe3 (v751 r t b x y) (v755 r t b x y) (v753 r t b x y) (v777 r t b x y) (v776 r t b x y)
  dsimp only at h
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41⟩
  have saddOverflow : (v791 r t b x y).saddOverflow (19#64) = false := by
    simpa only [v758, v779, v782, v791, v793, BitVec.add_comm, BitVec.saddOverflow, Int.add_comm, Nat.add_comm] using h12
  have uaddOverflow : (v791 r t b x y).uaddOverflow (19#64) = false := by
    simpa only [v758, v779, v782, v791, v793, BitVec.add_comm, BitVec.uaddOverflow, Int.add_comm, Nat.add_comm] using h13
  simp only [v793,Operation.add,PoisonOr.value_bind,saddOverflow,uaddOverflow, Bool.false_eq_true, and_false,ite_false,PoisonOr.pure_def]

theorem safe795 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    Operation.add {nsw := true, nuw := true}
      (.value ((v761 r t b x y))) (.value ((v794 r t b x y))) = .value (v795 r t b x y) := by
  have h := RIR.toBytesSafe3 (v751 r t b x y) (v755 r t b x y) (v753 r t b x y) (v777 r t b x y) (v776 r t b x y)
  dsimp only at h
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41⟩
  have saddOverflow : (v761 r t b x y).saddOverflow ((v794 r t b x y)) = false := by
    simpa only [v754, v758, v759, v761, v779, v782, v791, v793, v794, v795, BitVec.add_comm, BitVec.saddOverflow, Int.add_comm, Nat.add_comm] using h14
  have uaddOverflow : (v761 r t b x y).uaddOverflow ((v794 r t b x y)) = false := by
    simpa only [v754, v758, v759, v761, v779, v782, v791, v793, v794, v795, BitVec.add_comm, BitVec.uaddOverflow, Int.add_comm, Nat.add_comm] using h15
  simp only [v795,Operation.add,PoisonOr.value_bind,saddOverflow,uaddOverflow, Bool.false_eq_true, and_false,ite_false,PoisonOr.pure_def]

theorem safe797 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    Operation.add {nsw := true, nuw := true}
      (.value ((v762 r t b x y))) (.value ((v796 r t b x y))) = .value (v797 r t b x y) := by
  have h := RIR.toBytesSafe3 (v751 r t b x y) (v755 r t b x y) (v753 r t b x y) (v777 r t b x y) (v776 r t b x y)
  dsimp only at h
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41⟩
  have saddOverflow : (v762 r t b x y).saddOverflow ((v796 r t b x y)) = false := by
    simpa only [v754, v756, v758, v759, v760, v761, v762, v779, v782, v791, v793, v794, v795, v796, v797, BitVec.add_comm, BitVec.saddOverflow, Int.add_comm, Nat.add_comm] using h16
  have uaddOverflow : (v762 r t b x y).uaddOverflow ((v796 r t b x y)) = false := by
    simpa only [v754, v756, v758, v759, v760, v761, v762, v779, v782, v791, v793, v794, v795, v796, v797, BitVec.add_comm, BitVec.uaddOverflow, Int.add_comm, Nat.add_comm] using h17
  simp only [v797,Operation.add,PoisonOr.value_bind,saddOverflow,uaddOverflow, Bool.false_eq_true, and_false,ite_false,PoisonOr.pure_def]

theorem safe799 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    Operation.add {nsw := true, nuw := true}
      (.value ((v792 r t b x y))) (.value ((v798 r t b x y))) = .value (v799 r t b x y) := by
  have h := RIR.toBytesSafe3 (v751 r t b x y) (v755 r t b x y) (v753 r t b x y) (v777 r t b x y) (v776 r t b x y)
  dsimp only at h
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41⟩
  have saddOverflow : (v792 r t b x y).saddOverflow ((v798 r t b x y)) = false := by
    simpa only [v754, v756, v757, v758, v759, v760, v761, v762, v779, v780, v782, v791, v792, v793, v794, v795, v796, v797, v798, v799, BitVec.add_comm, BitVec.saddOverflow, Int.add_comm, Nat.add_comm] using h18
  have uaddOverflow : (v792 r t b x y).uaddOverflow ((v798 r t b x y)) = false := by
    simpa only [v754, v756, v757, v758, v759, v760, v761, v762, v779, v780, v782, v791, v792, v793, v794, v795, v796, v797, v798, v799, BitVec.add_comm, BitVec.uaddOverflow, Int.add_comm, Nat.add_comm] using h19
  simp only [v799,Operation.add,PoisonOr.value_bind,saddOverflow,uaddOverflow, Bool.false_eq_true, and_false,ite_false,PoisonOr.pure_def]

theorem safe801 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    Operation.add {nsw := true, nuw := true}
      (.value ((v783 r t b x y))) (.value ((v800 r t b x y))) = .value (v801 r t b x y) := by
  have h := RIR.toBytesSafe3 (v751 r t b x y) (v755 r t b x y) (v753 r t b x y) (v777 r t b x y) (v776 r t b x y)
  dsimp only at h
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41⟩
  have saddOverflow : (v783 r t b x y).saddOverflow ((v800 r t b x y)) = false := by
    simpa only [v754, v756, v757, v758, v759, v760, v761, v762, v778, v779, v780, v781, v782, v783, v791, v792, v793, v794, v795, v796, v797, v798, v799, v800, v801, BitVec.add_comm, BitVec.saddOverflow, Int.add_comm, Nat.add_comm] using h20
  have uaddOverflow : (v783 r t b x y).uaddOverflow ((v800 r t b x y)) = false := by
    simpa only [v754, v756, v757, v758, v759, v760, v761, v762, v778, v779, v780, v781, v782, v783, v791, v792, v793, v794, v795, v796, v797, v798, v799, v800, v801, BitVec.add_comm, BitVec.uaddOverflow, Int.add_comm, Nat.add_comm] using h21
  simp only [v801,Operation.add,PoisonOr.value_bind,saddOverflow,uaddOverflow, Bool.false_eq_true, and_false,ite_false,PoisonOr.pure_def]

theorem safe803 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    Operation.add {nsw := true, nuw := true}
      (.value ((v802 r t b x y))) (.value ((v791 r t b x y))) = .value (v803 r t b x y) := by
  unfold v803
  apply small_add
  · have h := (v801 r t b x y).isLt
    simp [v802, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  · have h := weakWord_bound (fun i => ![v751 r t b x y, v755 r t b x y, v753 r t b x y, v777 r t b x y, v776 r t b x y] i) 0
    simpa [weakWord, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val, v791,v782,v779,v758] using (show (weakWord (fun i => ![v751 r t b x y, v755 r t b x y, v753 r t b x y, v777 r t b x y, v776 r t b x y] i) 0).toNat < 2^60 by norm_num [radix] at h ⊢; omega)

theorem safe808 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    Operation.add {nsw := true, nuw := true}
      (.value ((v790 r t b x y))) (.value ((v767 r t b x y))) = .value (v808 r t b x y) := by
  simpa only [v767, v786, v790, v808] using fold_operation (v784 r t b x y) (v763 r t b x y)

theorem safe809 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    BinOp.compute (BinOp.vector (BinOp.add {nsw := true, nuw := true}))
      (Ty.wrap (v789 r t b x y)) (Ty.wrap (v807 r t b x y)) = Ty.wrap (v809 r t b x y) := by
  simp [v789, v807, v809, BinOp.compute, vector_two, mlir_operation,
    SerialPoint.weak_mul_nooverflow, SerialPoint.weak_fold_nooverflow, SerialPoint.weak_carry_add_nooverflow]

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline956

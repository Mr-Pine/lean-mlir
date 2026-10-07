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

def selected (b : BitVec 8) (x y : Words) : Words := fun i => choose b (x i) (y i)

theorem selected_byte (b : Bool) (x y : Words) :
    selected (byte b) x y = if b then y else x := by
  funext i
  simp only [selected, choose_byte]
  cases b <;> rfl

theorem selected751 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    v751 r t b x y = selected b x y 0 := by rfl

theorem selected755 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    v755 r t b x y = selected b x y 1 := by rfl

theorem selected753 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    v753 r t b x y = selected b x y 2 := by rfl

theorem selected777 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    v777 r t b x y = selected b x y 3 := by rfl

theorem selected776 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    v776 r t b x y = selected b x y 4 := by rfl

theorem selected750 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    v750 r t b x y = #v[selected b x y 0, selected b x y 1] := by rfl

theorem selected752 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    v752 r t b x y = #v[selected b x y 1, selected b x y 2] := by rfl

theorem selected775 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    v775 r t b x y = #v[selected b x y 3, selected b x y 4] := by rfl

attribute [local irreducible] v751 v755 v753 v777 v776 selected

theorem negative_high_mask (a : BitVec 64) :
    (2251799813685232#64 - a) &&& 2251799813685247#64 =
      (36028797018963952#64 - a) &&& 2251799813685247#64 := by
  have hlow : (2251799813685232#64 - a).setWidth 51 =
      (36028797018963952#64 - a).setWidth 51 := by
    simp only [BitVec.sub_eq_add_neg,
      BitVec.setWidth_add _ _ (by decide : 51 ≤ 64),
      BitVec.setWidth_neg_of_le (by decide : 51 ≤ 64)]
    rfl
  have hleft := BitVec.and_setWidth_allOnes 13 51 (2251799813685232#64 - a)
  have hright := BitVec.and_setWidth_allOnes 13 51 (36028797018963952#64 - a)
  change (2251799813685232#64 - a) &&& 2251799813685247#64 =
    0#13 ++ (2251799813685232#64 - a).setWidth 51 at hleft
  change (36028797018963952#64 - a) &&& 2251799813685247#64 =
    0#13 ++ (36028797018963952#64 - a).setWidth 51 at hright
  exact hleft.trans ((congrArg (fun b : BitVec 51 => 0#13 ++ b) hlow).trans hright.symm)

theorem parity_expression (r t : Pointer) (b : BitVec 8) (x y : Words) :
    v805 r t b x y =
      ((quotientWord (selected b x y) + weakWord (selected b x y) 0).setWidth 8 &&& 1#8) := by
  simp only [v754, v756, v757, v758, v759, v760, v761, v762, v763, v764, v765, v766, v767, v768, v769, v770, v771, v772, v773, v774, v778, v779, v780, v781, v782, v783, v784, v785, v786, v787, v788, v789, v790, v791, v792, v793, v794, v795, v796, v797, v798, v799, v800, v801, v802, v803, v804, v805,
    selected751, selected755, selected753, selected777, selected776,
    quotientWord, carriedWord, weakWord, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  rfl

/-- The omitted factor nineteen does not change the parity bit. -/
theorem parity_mul19 (q w : BitVec 64) :
    (q + w).setWidth 8 &&& 1#8 = (w + 19#64 * q).setWidth 8 &&& 1#8 := by
  have hlow : (q + w).setWidth 1 = (w + 19#64 * q).setWidth 1 := by
    simp only [BitVec.setWidth_add _ _ (by decide : 1 ≤ 64),
      BitVec.setWidth_mul _ _ (by decide : 1 ≤ 64)]
    change q.setWidth 1 + w.setWidth 1 = w.setWidth 1 + 1#1 * q.setWidth 1
    simp [BitVec.add_comm]
  have hl := BitVec.and_setWidth_allOnes 7 1 ((q + w).setWidth 8)
  have hr := BitVec.and_setWidth_allOnes 7 1 ((w + 19#64 * q).setWidth 8)
  change (q + w).setWidth 8 &&& 1#8 = 0#7 ++ ((q + w).setWidth 8).setWidth 1 at hl
  change (w + 19#64 * q).setWidth 8 &&& 1#8 =
    0#7 ++ ((w + 19#64 * q).setWidth 8).setWidth 1 at hr
  simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 1 ≤ 8)] at hl hr
  exact hl.trans ((congrArg (fun a : BitVec 1 => 0#7 ++ a) hlow).trans hr.symm)

theorem mask_one (w : BitVec 256) :
    w.setWidth 8 &&& 1#8 = byte (decide (w.toNat % 2 = 1)) := by
  have h := Nat.mod_lt w.toNat (by decide : 0 < 2)
  have ha : (w.setWidth 8 &&& 1#8).toNat = w.toNat % 2 := by
    simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    change (w.toNat % 256) &&& (2^1 - 1) = w.toNat % 2
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [ha]
  unfold byte
  split <;> simp_all <;> omega

theorem canonical_low (x : Words) :
    (canonicalWord x).setWidth 8 &&& 1#8 =
      (weakWord x 0 + 19#64 * quotientWord x).setWidth 8 &&& 1#8 := by
  have h := BitVec.setWidth_append (k := 8)
    (x := (0#1 ++ tightWords x 4 ++ tightWords x 3 ++ tightWords x 2 ++ tightWords x 1))
    (y := tightWords x 0)
  simp only [show (8 : Nat) ≤ 51 by decide, dite_true] at h
  rw [canonicalWord, packedBytes_eq, h]
  simp [tightWords,carriedWord]

theorem parity_semantic (r t : Pointer) (b : BitVec 8) (x y : Words) :
    v805 r t b x y = byte (decide ((canonicalWord (selected b x y)).toNat % 2 = 1)) := by
  rw [parity_expression, parity_mul19, ← canonical_low, mask_one]

def rootWords (r t : Pointer) (b : BitVec 8) (x y : Words) : Words :=
  ![v814 r t b x y, (v818 r t b x y)[0], (v818 r t b x y)[1],
    (v821 r t b x y)[0], (v821 r t b x y)[1]]

theorem negative808 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    v808 r t b x y = emittedNegativeWords (selected b x y) 0 := by
  simp only [v808,v790,v786,v784,v767,v763,selected751,selected776,
    emittedNegativeWords, Matrix.cons_val_zero]

theorem negative769 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    v769 r t b x y = #v[emittedNegativeWords (selected b x y) 1,
      emittedNegativeWords (selected b x y) 2] := by
  simp [v769,v768,v765,v766,v764,selected750,selected752,
    emittedNegativeWords, negative_high_mask, BitVec.add_comm]

theorem negative809 (r t : Pointer) (b : BitVec 8) (x y : Words) :
    v809 r t b x y = #v[emittedNegativeWords (selected b x y) 3,
      emittedNegativeWords (selected b x y) 4] := by
  simp [v809,v789,v785,v807,v788,v787,selected775,selected752,
    emittedNegativeWords, negative_high_mask, BitVec.add_comm]

theorem rootWords_selected (r t : Pointer) (b : BitVec 8) (x y : Words) :
    rootWords r t b x y =
      fun i => choose (v805 r t b x y) (selected b x y i)
        (emittedNegativeWords (selected b x y) i) := by
  funext i
  fin_cases i <;>
    simp [rootWords,v814,v813,v812,v811,v810,v806,v818,v817,v816,
      v770,v821,v820,v819,negative808,negative769,negative809,
      v751,v750,v748,v744,v740,v741,v752,v749,v745,v742,v743,
      v775,v774,v773,v771,v772,v747,v735,v734,selected,choose]

theorem rootWords_nonnegative (r t : Pointer) (b : BitVec 8) (x y : Words) :
    rootWords r t b x y =
      if decide ((canonicalWord (selected b x y)).toNat % 2 = 1) then
        negativeWords (selected b x y) else selected b x y := by
  rw [rootWords_selected, parity_semantic]
  funext i
  simp only [choose_byte, emittedNegativeWords_eq]
  split <;> rfl

/-- Semantic root identification uses incoming word data, never an execution premise. -/
theorem rootWords_sqrt (r t : Pointer) (u v : Pow22501.TightWords) :
    rootWords r t
      (byte (equalWords (wordCheck u v) (negativeWord u) ||
        equalWords (wordCheck u v) ((negativeWord u).mul sqrtM1Word)))
      (wordCandidate u v).limbs (sqrtM1Word.mul (wordCandidate u v)).limbs =
        (wordSqrt u v).2.limbs := by
  rw [rootWords_nonnegative, selected_byte]
  unfold wordSqrt wordNonnegative wordCorrected oddWord negativeWord
  split <;> simp_all
  all_goals split <;> simp_all

/-- The retained comparison bytes form the exact returned square predicate. -/
theorem flag_sqrt (u v : Pow22501.TightWords) :
    byte (equalWords (wordCheck u v) (negativeWord u)) |||
      byte (equalWords (wordCheck u v) u) = byte (wordSqrt u v).1 := by
  unfold byte
  rw [choice_or]
  unfold wordSqrt
  rw [Bool.or_comm]

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline956

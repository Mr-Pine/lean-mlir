import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Arithmetic

/-! A word-level statement of the reduction calculation. The RIR execution
bridge is separate: this file proves that the wrapping operations used there
implement the integer carry schedule when the columns satisfy `ColumnsBound`. -/
namespace Agave.Ed25519.Reduce64.Word
abbrev Columns := Fin 10 → BitVec 64

def t1 (z : Columns) := z 1 + (z 0 >>> 26)
def t2 (z : Columns) := z 2 + (t1 z >>> 25)
def t3 (z : Columns) := z 3 + (t2 z >>> 26)
def t5 (z : Columns) := z 5 + (z 4 >>> 26)
def t6 (z : Columns) := z 6 + (t5 z >>> 25)
def t7 (z : Columns) := z 7 + (t6 z >>> 26)
def t4 (z : Columns) := (z 4 &&& 67108863#64) + (t3 z >>> 25)
def u5 (z : Columns) := (t5 z &&& 33554431#64) + (t4 z >>> 26)
def t8 (z : Columns) := z 8 + (t7 z >>> 25)
def t9 (z : Columns) := z 9 + (t8 z >>> 26)
def carry (z : Columns) := t9 z >>> 25
def u0 (z : Columns) := (z 0 &&& 67108863#64) + (carry z &&& 67108863#64) * 19#64
def u1 (z : Columns) := (t1 z &&& 33554431#64) + (carry z >>> 26) * 19#64 + (u0 z >>> 26)
def reduce (z : Columns) : Columns :=
  ![u0 z &&& 67108863#64, u1 z, t2 z &&& 67108863#64, t3 z &&& 33554431#64,
    t4 z &&& 67108863#64, u5 z, t6 z &&& 67108863#64, t7 z &&& 33554431#64,
    t8 z &&& 67108863#64, t9 z &&& 33554431#64]

theorem mask26_toNat (x : BitVec 64) :
    (x &&& 67108863#64).toNat = x.toNat % 2^26 := by
  change x.toNat &&& (2^26 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem mask25_toNat (x : BitVec 64) :
    (x &&& 33554431#64).toNat = x.toNat % 2^25 := by
  change x.toNat &&& (2^25 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod _ _

/-- All ten machine-word outputs equal their natural-number specifications. -/
theorem toNat_reduce (z : Columns)
    (h : Reduce64.ColumnsBound (fun i => (z i).toNat)) (i : Fin 10) :
    (reduce z i).toNat = Reduce64.reduce (fun j => (z j).toNat) i := by
  let n : Reduce64.Columns := fun j => (z j).toNat
  obtain ⟨hb1,hb2,hb3,hb5,hb6,hb7,hb8,hb9⟩ := Reduce64.no_unsigned_wrap n h
  obtain ⟨hs4,hs5,hml,hmh,hs0,hs1⟩ := Reduce64.small_intermediate_bounds n h
  have ht1 : (t1 z).toNat = Reduce64.t1 n := by
    simp only [t1, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt hb1
  have ht2 : (t2 z).toNat = Reduce64.t2 n := by
    simp only [t2, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ht1]
    exact Nat.mod_eq_of_lt hb2
  have ht3 : (t3 z).toNat = Reduce64.t3 n := by
    simp only [t3, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ht2]
    exact Nat.mod_eq_of_lt hb3
  have ht5 : (t5 z).toNat = Reduce64.t5 n := by
    simp only [t5, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt hb5
  have ht6 : (t6 z).toNat = Reduce64.t6 n := by
    simp only [t6, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ht5]
    exact Nat.mod_eq_of_lt hb6
  have ht7 : (t7 z).toNat = Reduce64.t7 n := by
    simp only [t7, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ht6]
    exact Nat.mod_eq_of_lt hb7
  have ht8 : (t8 z).toNat = Reduce64.t8 n := by
    simp only [t8, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ht7]
    exact Nat.mod_eq_of_lt hb8
  have ht9 : (t9 z).toNat = Reduce64.t9 n := by
    simp only [t9, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ht8]
    exact Nat.mod_eq_of_lt hb9
  have ht4 : (t4 z).toNat = Reduce64.t4 n := by
    simp only [t4, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, mask26_toNat, ht3]
    exact Nat.mod_eq_of_lt (lt_trans hs4 (show (2:Nat)^40 < 2^64 by norm_num))
  have hu5 : (u5 z).toNat = Reduce64.u5 n := by
    simp only [u5, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, mask25_toNat, ht5, ht4]
    exact Nat.mod_eq_of_lt (lt_trans hs5 (show (2:Nat)^26 < 2^64 by norm_num))
  have hc : (carry z).toNat = Reduce64.carry n := by
    simp only [carry, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ht9]
    rfl
  have hml' : (((carry z &&& 67108863#64) * 19#64).toNat) =
      (Reduce64.carry n % 2^26) * 19 := by
    simp only [BitVec.toNat_mul, mask26_toNat, hc]
    norm_num
    exact lt_trans hml (show (2:Nat)^31 < 2^64 by norm_num)
  have hmh' : (((carry z >>> 26) * 19#64).toNat) =
      (Reduce64.carry n / 2^26) * 19 := by
    simp only [BitVec.toNat_mul, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, hc]
    norm_num
    exact lt_trans hmh (show (2:Nat)^18 < 2^64 by norm_num)
  have hu0 : (u0 z).toNat = Reduce64.u0 n := by
    simp only [u0, BitVec.toNat_add, mask26_toNat, hml']
    exact Nat.mod_eq_of_lt (lt_trans hs0 (show (2:Nat)^31 < 2^64 by norm_num))
  have hf : ((t1 z &&& 33554431#64) + (carry z >>> 26) * 19#64).toNat =
      Reduce64.t1 n % 2^25 + (Reduce64.carry n / 2^26) * 19 := by
    simp only [BitVec.toNat_add, mask25_toNat, ht1, hmh']
    apply Nat.mod_eq_of_lt
    unfold Reduce64.u1 at hs1
    norm_num at hs1 ⊢
    omega
  have hu1 : (u1 z).toNat = Reduce64.u1 n := by
    rw [u1, BitVec.toNat_add, hf, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, hu0]
    exact Nat.mod_eq_of_lt (lt_trans hs1 (show (2:Nat)^26 < 2^64 by norm_num))
  fin_cases i <;>
    simp [reduce, Reduce64.reduce, mask26_toNat, mask25_toNat,
      ht2, ht3, ht4, hu5, ht6, ht7, ht8, ht9, hu0, hu1, n]
  all_goals first | exact Nat.and_two_pow_sub_one_eq_mod _ 26 | exact Nat.and_two_pow_sub_one_eq_mod _ 25

end Agave.Ed25519.Reduce64.Word

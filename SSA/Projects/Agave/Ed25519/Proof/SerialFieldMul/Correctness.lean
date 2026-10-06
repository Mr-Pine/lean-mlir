module
public import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Algebra
public import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Machine
public import Mathlib.Data.BitVec

namespace Agave.Ed25519.SerialFieldMul
@[expose] public section

abbrev unsigned (a : Fin 5 → BitVec 64) : Limbs := fun i => (a i).toNat

/-- Machine columns in exactly the LLVM sum order. -/
def wordColumns (a b : Fin 5 → BitVec 64) : Fin 5 → BitVec 128 :=
  let A := fun i => (a i).setWidth 128
  let B := fun i => (b i).setWidth 128
  let B19 := fun i => (b i * 19).setWidth 128
  ![(((A 4*B19 1 + B 0*A 0) + A 3*B19 2) + A 2*B19 3) + A 1*B19 4,
    (((A 4*B19 2 + A 0*B 1) + A 3*B19 3) + A 2*B19 4) + A 1*B 0,
    (((A 4*B19 3 + A 0*B 2) + A 3*B19 4) + A 2*B 0) + A 1*B 1,
    (((A 4*B19 4 + A 0*B 3) + A 3*B 0) + A 2*B 1) + A 1*B 2,
    (((A 4*B 0 + A 0*B 4) + A 3*B 1) + A 2*B 2) + A 1*B 3]

def wordSchedule (c : Fin 5 → BitVec 128) : Fin 5 → BitVec 64 :=
  let carry := fun x : BitVec 128 => (x >>> 51) &&& 18446744073709551615#128
  let low := fun x : BitVec 128 => x.setWidth 64 &&& 2251799813685247#64
  let t0 := c 0
  let t1 := c 1 + carry t0
  let t2 := c 2 + carry t1
  let t3 := c 3 + carry t2
  let t4 := c 4 + carry t3
  let f := ((t4 >>> 51).setWidth 64)*19 + low t0
  ![f &&& 2251799813685247#64, (f >>> 51) + low t1, low t2, low t3, low t4]

/-- Definitional equality checks every generated machine expression against the schedule. -/
theorem machine_eq_schedule (a b : Fin 5 → BitVec 64) :
    machine a b = wordSchedule (wordColumns a b) := rfl

theorem widen_eq_cast (x : BitVec 64) : x.setWidth 128 = (x.toNat : BitVec 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128),
    BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have hx := x.isLt
  norm_num at hx ⊢
  omega

theorem widen_scale_eq_cast (x : BitVec 64) (hx : x.toNat < 2^54) :
    (x*19).setWidth 128 = ((x.toNat*19 : Nat) : BitVec 128) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128), BitVec.toNat_mul,
    BitVec.toNat_ofNat, BitVec.natCast_eq_ofNat]
  norm_num
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The word columns are casts of the integer convolution. -/
theorem wordColumns_eq (a b : Fin 5 → BitVec 64) (hb : Bounded (unsigned b)) :
    wordColumns a b = fun i => (columns (unsigned a) (unsigned b) i : BitVec 128) := by
  have hs (i : Fin 5) : (b i * 19).setWidth 128 =
      ((unsigned b i * 19 : Nat) : BitVec 128) := widen_scale_eq_cast _ (hb i)
  funext i
  fin_cases i <;> simp only [wordColumns, hs] <;>
    simp [columns, widen_eq_cast,
      unsigned, Nat.cast_add, Nat.cast_mul, -BitVec.natCast_eq_ofNat, -BitVec.ofNat_toNat] <;> ring

/-- The carry truncation is exact under the wide-column bound. -/
theorem word_carry (n : Nat) (hn : n < 2^115) :
    (((n : BitVec 128) >>> 51) &&& 18446744073709551615#128) =
      ((n / radix : Nat) : BitVec 128) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.natCast_eq_ofNat,
    BitVec.toNat_ofNat]
  change ((n % 2^128 / 2^51) &&& (2^64-1)) = (n / radix) % 2^128
  rw [Nat.and_two_pow_sub_one_eq_mod]
  norm_num [radix] at *
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

/-- Low 51 bits are independent of the intermediate word truncations. -/
theorem word_low (n : Nat) :
    (n : BitVec 128).setWidth 64 &&& 2251799813685247#64 =
      ((n % radix : Nat) : BitVec 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.natCast_eq_ofNat,
    BitVec.toNat_ofNat]
  change ((n % 2^128 % 2^64) &&& (2^51-1)) = (n % radix) % 2^64
  rw [Nat.and_two_pow_sub_one_eq_mod]
  norm_num [radix]
  omega

theorem word_top (n : Nat) (hn : n < 2^128) :
    ((n : BitVec 128) >>> 51).setWidth 64 = ((n / radix : Nat) : BitVec 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hn]

theorem word_low64 (n : Nat) :
    (n : BitVec 64) &&& 2251799813685247#64 = ((n % radix : Nat) : BitVec 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
  change ((n % 2^64) &&& (2^51-1)) = (n % radix) % 2^64
  rw [Nat.and_two_pow_sub_one_eq_mod]
  norm_num [radix]
  omega

theorem word_shift64 (n : Nat) (hn : n < 2^64) :
    ((n : BitVec 64) >>> 51) = ((n / radix : Nat) : BitVec 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by norm_num [radix] at *; omega)]

theorem word_step (x y : Nat) (hy : y < 2^115) :
    (x : BitVec 128) + (((y : BitVec 128) >>> 51) &&& 18446744073709551615#128) =
      ((x + y / radix : Nat) : BitVec 128) := by
  rw [word_carry y hy]
  exact (Nat.cast_add x (y / radix)).symm

/-- Word truncations preserve the natural-number schedule under its derived bounds. -/
theorem wordSchedule_eq (c : Limbs)
    (hc : ∀ i, carried c i < 2^115) (hf : folded c < 2^64) :
    wordSchedule (fun i => (c i : BitVec 128)) =
      fun i => (reduce c i : BitVec 64) := by
  have h1 : (c 1 : BitVec 128) + (((c 0 : BitVec 128) >>> 51) &&& 18446744073709551615#128) =
      (carried c 1 : BitVec 128) := word_step (c 1) (c 0) (hc 0)
  have h2 : (c 2 : BitVec 128) + (((carried c 1 : BitVec 128) >>> 51) &&& 18446744073709551615#128) =
      (carried c 2 : BitVec 128) := word_step (c 2) (carried c 1) (hc 1)
  have h3 : (c 3 : BitVec 128) + (((carried c 2 : BitVec 128) >>> 51) &&& 18446744073709551615#128) =
      (carried c 3 : BitVec 128) := word_step (c 3) (carried c 2) (hc 2)
  have h4 : (c 4 : BitVec 128) + (((carried c 3 : BitVec 128) >>> 51) &&& 18446744073709551615#128) =
      (carried c 4 : BitVec 128) := word_step (c 4) (carried c 3) (hc 3)
  have ht := word_top (carried c 4) (show carried c 4 < 2^128 by have := hc 4; omega)
  have hfcast : (((carried c 4 / radix : Nat) : BitVec 64)*19 + ((c 0 % radix : Nat) : BitVec 64)) =
      (folded c : BitVec 64) := by
    simp only [folded, Nat.cast_add, Nat.cast_mul]
    ring
  funext i
  simp only [wordSchedule, h1, h2, h3, h4, ht, word_low, hfcast,
    word_low64, word_shift64 _ hf]
  fin_cases i <;> simp [reduce, Nat.cast_add, add_comm]

/-- All arithmetic in the compiler-emitted word expression implements the field
multiplication carry schedule under the Rust kernel's caller invariant. -/
theorem machine_eq_reduce (a b : Fin 5 → BitVec 64)
    (ha : Bounded (unsigned a)) (hb : Bounded (unsigned b)) :
    machine a b = fun i => (reduce (columns (unsigned a) (unsigned b)) i : BitVec 64) := by
  rw [machine_eq_schedule, wordColumns_eq a b hb]
  exact wordSchedule_eq _ (carried_bounds _ _ ha hb).1 (carried_bounds _ _ ha hb).2

theorem machine_unsigned (a b : Fin 5 → BitVec 64)
    (ha : Bounded (unsigned a)) (hb : Bounded (unsigned b)) :
    unsigned (machine a b) = reduce (columns (unsigned a) (unsigned b)) := by
  funext i
  rw [machine_eq_reduce a b ha hb]
  simp only [unsigned, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have h := (mul_output_bounds _ _ ha hb).2.2 i
  norm_num at h ⊢
  omega

/-- Modular correctness of the actual compiler-emitted bitvector expression. -/
theorem machine_correct (a b : Fin 5 → BitVec 64)
    (ha : Bounded (unsigned a)) (hb : Bounded (unsigned b)) :
    decode (unsigned (machine a b)) % modulus =
      (decode (unsigned a) * decode (unsigned b)) % modulus := by
  rw [machine_unsigned a b ha hb]
  exact reduce_columns_mod _ _

end
end Agave.Ed25519.SerialFieldMul

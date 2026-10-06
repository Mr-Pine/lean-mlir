import SSA.Projects.Agave.Ed25519.Proof.Encoding.BytePacking
import SSA.Projects.Agave.Ed25519.Proof.Encoding.WordBounds

namespace Agave.Ed25519.Encoding

def weakWord (a : Field.Serial) : Field.Serial := ![
  (a 4 >>> 51) * 19 + (a 0 &&& 2251799813685247),
  (a 1 &&& 2251799813685247) + (a 0 >>> 51),
  (a 2 &&& 2251799813685247) + (a 1 >>> 51),
  (a 3 &&& 2251799813685247) + (a 2 >>> 51),
  (a 4 &&& 2251799813685247) + (a 3 >>> 51)]

def carriedWord (a : Field.Serial) (extra : BitVec 64) : Field.Serial :=
  let t0 := a 0 + extra
  let t1 := a 1 + (t0 >>> 51)
  let t2 := a 2 + (t1 >>> 51)
  let t3 := a 3 + (t2 >>> 51)
  let t4 := a 4 + (t3 >>> 51)
  ![t0, t1, t2, t3, t4]

def quotientWord (a : Field.Serial) : BitVec 64 := carriedWord (weakWord a) 19 4 >>> 51

def tightWords (a : Field.Serial) : Fin 5 → BitVec 51 :=
  fun i => (carriedWord (weakWord a) (19 * quotientWord a) i).setWidth 51

theorem word_mask51_nat (a : BitVec 64) :
    (a &&& 2251799813685247).toNat = a.toNat % 2^51 := by
  rw [BitVec.toNat_and]
  change a.toNat &&& (2^51 - 1) = a.toNat % 2^51
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem weakWord_toNat (a : Field.Serial) (i : Fin 5) :
    (weakWord a i).toNat = weakReduce (fun j => (a j).toNat) i := by
  have h0 := (a 0).isLt; have h1 := (a 1).isLt; have h2 := (a 2).isLt
  have h3 := (a 3).isLt; have h4 := (a 4).isLt
  have hm0 := word_mask51_nat (a 0); have hm1 := word_mask51_nat (a 1)
  have hm2 := word_mask51_nat (a 2); have hm3 := word_mask51_nat (a 3)
  have hm4 := word_mask51_nat (a 4)
  fin_cases i <;>
    norm_num [weakWord, weakReduce, radix, BitVec.toNat_add, BitVec.toNat_mul,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, word_mask51_nat] at * <;>
    omega

theorem carriedWord_toNat (a : Field.Serial) (extra : BitVec 64)
    (ha : ∀ i, (a i).toNat < radix + 19 * 2^13) (he : extra.toNat ≤ 19)
    (i : Fin 5) :
    (carriedWord a extra i).toNat = carried (fun j => (a j).toNat) extra.toNat i := by
  have h0 := ha 0; have h1 := ha 1; have h2 := ha 2; have h3 := ha 3; have h4 := ha 4
  fin_cases i <;>
    norm_num [carriedWord, carried, radix, BitVec.toNat_add,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at * <;>
    omega

theorem weakWord_bound (a : Field.Serial) (i : Fin 5) :
    (weakWord a i).toNat < radix + 19 * 2^13 := by
  rw [weakWord_toNat]
  exact weakReduce_limb_bound _ (fun j => (a j).isLt) i

theorem quotientWord_toNat (a : Field.Serial) :
    (quotientWord a).toNat = quotient (weakReduce (fun i => (a i).toNat)) := by
  rw [quotientWord, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    carriedWord_toNat _ _ (weakWord_bound a) (by decide)]
  simp only [weakWord_toNat]
  rfl

theorem quotientWord_mul19_toNat (a : Field.Serial) :
    (19 * quotientWord a).toNat =
      19 * quotient (weakReduce (fun i => (a i).toNat)) := by
  have hq := quotient_weakReduce_le_one (fun i => (a i).toNat) (fun i => (a i).isLt)
  rw [BitVec.toNat_mul, quotientWord_toNat]
  norm_num
  omega

theorem tightWords_toNat (a : Field.Serial) (i : Fin 5) :
    (tightWords a i).toNat = canonicalLimbs (fun j => (a j).toNat) i := by
  have he : (19 * quotientWord a).toNat ≤ 19 := by
    rw [quotientWord_mul19_toNat]
    have hq := quotient_weakReduce_le_one (fun j => (a j).toNat) (fun j => (a j).isLt)
    omega
  rw [tightWords, BitVec.toNat_setWidth,
    carriedWord_toNat _ _ (weakWord_bound a) he]
  simp only [weakWord_toNat, quotientWord_mul19_toNat]
  rfl

theorem tightWords_canonical (a : Field.Serial) :
    (packedBytes (tightWords a)).toNat = Field.serialValue a % modulus := by
  rw [packedBytes_toNat]
  simp only [tightWords_toNat]
  rw [canonicalLimbs_value _ (fun i => (a i).isLt), value_eq_decode51]
  rfl

end Agave.Ed25519.Encoding

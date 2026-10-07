import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputSplitWords

/-! Positional interpretation of the exact ten wrapper split words. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open Agave.Ed25519.ScalarReduce32.Arithmetic
open ScalarMontgomeryMul
set_option exponentiation.threshold 1024

/-- Five radix-52 digits reconstruct the low 260 bits of any natural number. -/
theorem fiveDigits_value (n : Nat) :
    limbs (n % 2 ^ 52) (n / 2 ^ 52 % 2 ^ 52) (n / 2 ^ 104 % 2 ^ 52)
      (n / 2 ^ 156 % 2 ^ 52) (n / 2 ^ 208 % 2 ^ 52) = n % 2 ^ 260 := by
  have h0 := Nat.mod_add_div n (2 ^ 52)
  have h1 := Nat.mod_add_div (n / 2 ^ 52) (2 ^ 52)
  have h2 := Nat.mod_add_div (n / 2 ^ 104) (2 ^ 52)
  have h3 := Nat.mod_add_div (n / 2 ^ 156) (2 ^ 52)
  have h4 := Nat.mod_add_div (n / 2 ^ 208) (2 ^ 52)
  have h5 := Nat.mod_add_div n (2 ^ 260)
  norm_num [limbs, radix, Nat.div_div_eq_div_mul] at h0 h1 h2 h3 h4 h5 ⊢
  omega

/-- The first actual Montgomery input is the low 260-bit half. -/
theorem lowSplitWords_value (bytes : BitVec 512) :
    limbValue (fun i => (lowSplitWords bytes i).toNat) = bytes.toNat % 2 ^ 260 := by
  have h := fiveDigits_value bytes.toNat
  simp only [limbValue, limbs, lowSplitWords_extract,
    BitVec.toNat_setWidth_of_le (by decide : 52 ≤ 64), BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  norm_num [limbs, radix] at h ⊢
  exact h

/-- The second actual Montgomery input is exactly the input shifted by 260. -/
theorem highSplitWords_value (bytes : BitVec 512) :
    limbValue (fun i => (highSplitWords bytes i).toNat) = bytes.toNat / 2 ^ 260 := by
  have h := fiveDigits_value (bytes.toNat / 2 ^ 260)
  have hb := bytes.isLt
  have hh : bytes.toNat / 2 ^ 260 < 2 ^ 260 := by
    norm_num at hb ⊢
    omega
  rw [Nat.mod_eq_of_lt hh] at h
  simp only [limbValue, limbs, highSplitWords_extract,
    BitVec.toNat_setWidth_of_le (by decide : 52 ≤ 64), BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  norm_num [limbs, radix, Nat.div_div_eq_div_mul] at h ⊢
  exact h

end Agave.Ed25519.Verifier.Execution.ScalarWide

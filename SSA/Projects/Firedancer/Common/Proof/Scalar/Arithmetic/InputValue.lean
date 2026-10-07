import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.InputDigits

namespace Firedancer.Common.ScalarArithmetic
open IntegerRegisters

/-- An arithmetic interpretation of concatenation, without replacing bit
operations by an unchecked numeric evaluator. -/
theorem append_natValue {m n : Nat} (x : BitVec m) (y : BitVec n) :
    ((x ++ y).toNat : Int) = (x.toNat : Int) * 2 ^ n + (y.toNat : Int) := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]
  push_cast
  rfl

def inputBits (digest : BitVec 512) : BitVec 512 :=
  digest.extractLsb' 483 29 ++
  digest.extractLsb' 462 21 ++
  digest.extractLsb' 441 21 ++
  digest.extractLsb' 420 21 ++
  digest.extractLsb' 399 21 ++
  digest.extractLsb' 378 21 ++
  digest.extractLsb' 357 21 ++
  digest.extractLsb' 336 21 ++
  digest.extractLsb' 315 21 ++
  digest.extractLsb' 294 21 ++
  digest.extractLsb' 273 21 ++
  digest.extractLsb' 252 21 ++
  digest.extractLsb' 231 21 ++
  digest.extractLsb' 210 21 ++
  digest.extractLsb' 189 21 ++
  digest.extractLsb' 168 21 ++
  digest.extractLsb' 147 21 ++
  digest.extractLsb' 126 21 ++
  digest.extractLsb' 105 21 ++
  digest.extractLsb' 84 21 ++
  digest.extractLsb' 63 21 ++
  digest.extractLsb' 42 21 ++
  digest.extractLsb' 21 21 ++
  digest.extractLsb' 0 21

theorem inputBits_eq (digest : BitVec 512) : inputBits digest = digest := by
  unfold inputBits
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 483) (len₂ := 29) (start₁ := 462) (len₁ := 21) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 462) (len₂ := 50) (start₁ := 441) (len₁ := 21) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 441) (len₂ := 71) (start₁ := 420) (len₁ := 21) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 420) (len₂ := 92) (start₁ := 399) (len₁ := 21) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 399) (len₂ := 113) (start₁ := 378) (len₁ := 21) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 378) (len₂ := 134) (start₁ := 357) (len₁ := 21) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 357) (len₂ := 155) (start₁ := 336) (len₁ := 21) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 336) (len₂ := 176) (start₁ := 315) (len₁ := 21) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 315) (len₂ := 197) (start₁ := 294) (len₁ := 21) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 294) (len₂ := 218) (start₁ := 273) (len₁ := 21) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 273) (len₂ := 239) (start₁ := 252) (len₁ := 21) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 252) (len₂ := 260) (start₁ := 231) (len₁ := 21) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 231) (len₂ := 281) (start₁ := 210) (len₁ := 21) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 210) (len₂ := 302) (start₁ := 189) (len₁ := 21) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 189) (len₂ := 323) (start₁ := 168) (len₁ := 21) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 168) (len₂ := 344) (start₁ := 147) (len₁ := 21) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 147) (len₂ := 365) (start₁ := 126) (len₁ := 21) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 126) (len₂ := 386) (start₁ := 105) (len₁ := 21) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 105) (len₂ := 407) (start₁ := 84) (len₁ := 21) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 84) (len₂ := 428) (start₁ := 63) (len₁ := 21) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 63) (len₂ := 449) (start₁ := 42) (len₁ := 21) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 42) (len₂ := 470) (start₁ := 21) (len₁ := 21) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 21) (len₂ := 491) (start₁ := 0) (len₁ := 21) (by decide)]
  simp

set_option maxHeartbeats 2000000 in
theorem inputValue_eq (digest : BitVec 512) :
    inputValue (inputDigits digest) = (digest.toNat : Int) := by
  calc
    inputValue (inputDigits digest) = ((inputBits digest).toNat : Int) := by
      simp only [inputValue, inputDigits, inputBits, append_natValue]
      norm_num
      ring
    _ = (digest.toNat : Int) := congrArg (fun v : BitVec 512 => (v.toNat : Int)) (inputBits_eq digest)

end Firedancer.Common.ScalarArithmetic

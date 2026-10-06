import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.Algebra

/-! Per-lane fixed-width operations from the Rust square kernel.
No result in this file claims the compiler-generated RIR has executed these
operations; the vector shuffle/bitcast execution connection is separate.
-/
namespace Agave.Ed25519.Avx2SquareNegateD
section

abbrev Raw := Fin 10 → BitVec 32

def mul32 (x y : BitVec 32) : BitVec 64 := x.setWidth 64 * y.setWidth 64

def twice (x : BitVec 32) : BitVec 32 := x <<< 1

def times19 (x : BitVec 32) : BitVec 32 := (19#64 * x.setWidth 64).setWidth 32

/-- Exact scalar projection of the ten source expressions, including every
32-bit doubling and low-word multiply before the 64-bit convolution. -/
def machineColumns (a : Raw) : Fin 10 → BitVec 64 := ![
  (mul32 (a 0) (a 0)) + (mul32 (twice (a 2)) (times19 (a 8))) + (mul32 (twice (a 4)) (times19 (a 6))) + (((mul32 (twice (a 1)) (times19 (a 9))) +   (mul32 (twice (a 3)) (times19 (a 7))) +    (mul32 (a 5) (times19 (a 5)))) <<< 1),
  (mul32 (twice (a 0)) (a 1)) + (mul32 (twice (a 3)) (times19 (a 8))) + (mul32 (twice (a 5)) (times19 (a 6))) +                    (((mul32 (a 2) (times19 (a 9))) +    (mul32 (a 4) (times19 (a 7)))) <<< 1),
  (mul32 (twice (a 0)) (a 2)) + (mul32 (twice (a 1)) (a 1)) + (mul32 (twice (a 4)) (times19 (a 8))) +   (mul32 (a 6) (times19 (a 6))) + (((mul32 (twice (a 3)) (times19 (a 9))) +    (mul32 (twice (a 5)) (times19 (a 7)))) <<< 1),
  (mul32 (twice (a 0)) (a 3)) + (mul32 (twice (a 1)) (a 2)) + (mul32 (twice (a 5)) (times19 (a 8))) +                    (((mul32 (a 4) (times19 (a 9))) +    (mul32 (a 6) (times19 (a 7)))) <<< 1),
  (mul32 (twice (a 0)) (a 4)) + (mul32 (twice (a 1)) (twice (a 3))) + (mul32 (a 2) (a 2)) +   (mul32 (twice (a 6)) (times19 (a 8))) + (((mul32 (twice (a 5)) (times19 (a 9))) +    (mul32 (a 7) (times19 (a 7)))) <<< 1),
  (mul32 (twice (a 0)) (a 5)) + (mul32 (twice (a 1)) (a 4)) + (mul32 (twice (a 2)) (a 3)) +   (mul32 (twice (a 7)) (times19 (a 8)))                    +  (((mul32 (a 6) (times19 (a 9))) <<< 1)),
  (mul32 (twice (a 0)) (a 6)) + (mul32 (twice (a 1)) (twice (a 5))) + (mul32 (twice (a 2)) (a 4)) +   (mul32 (twice (a 3)) (a 3)) +   (mul32 (a 8) (times19 (a 8))) +  (((mul32 (twice (a 7)) (times19 (a 9))) <<< 1)),
  (mul32 (twice (a 0)) (a 7)) + (mul32 (twice (a 1)) (a 6)) + (mul32 (twice (a 2)) (a 5)) +   (mul32 (twice (a 3)) (a 4))                    +  (((mul32 (a 8) (times19 (a 9))) <<< 1)),
  (mul32 (twice (a 0)) (a 8)) + (mul32 (twice (a 1)) (twice (a 7))) + (mul32 (twice (a 2)) (a 6)) +   (mul32 (twice (a 3)) (twice (a 5))) +   (mul32 (a 4) (a 4)) +  (((mul32 (a 9) (times19 (a 9))) <<< 1)),
  (mul32 (twice (a 0)) (a 9)) + (mul32 (twice (a 1)) (a 8)) + (mul32 (twice (a 2)) (a 7)) +   (mul32 (twice (a 3)) (a 6)) +   (mul32 (twice (a 4)) (a 5))                                 ]

theorem input_lt_u32 {a : Limbs} (ha : Bounded a) (i : Fin 10) : a i < 2^32 := by
  have h := input_double_lt_u32 ha i
  omega

private theorem shift_one_ofNat (a : Nat) :
    (BitVec.ofNat 64 a <<< 1) = BitVec.ofNat 64 (a*2) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 a * BitVec.ofNat 64 2 = _
  rw [← BitVec.ofNat_mul]

/-- Each actual narrow preparation step widens to its intended integer value;
these bounds are derived from the point caller rather than taken as premises. -/
theorem input_operations_exact {a : Limbs} (ha : Bounded a) (i : Fin 10) :
    (BitVec.ofNat 32 (a i)).setWidth 64 = BitVec.ofNat 64 (a i) ∧
    (twice (BitVec.ofNat 32 (a i))).setWidth 64 = BitVec.ofNat 64 (2*a i) ∧
    (times19 (BitVec.ofNat 32 (a i))).setWidth 64 = BitVec.ofNat 64 (19*a i) := by
  have hw := BitVec.setWidth_ofNat_of_le_of_lt (w := 32) (v := 64) (by decide) (input_lt_u32 ha i)
  refine ⟨hw, ?_, ?_⟩
  · unfold twice
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change ((BitVec.ofNat 32 (a i) * BitVec.ofNat 32 2).setWidth 64) = _
    rw [← BitVec.ofNat_mul]
    have hd : a i * 2 < 2^32 := by simpa [Nat.mul_comm] using input_double_lt_u32 ha i
    rw [BitVec.setWidth_ofNat_of_le_of_lt (w := 32) (v := 64) (by decide) hd]
    rw [Nat.mul_comm]
  · unfold times19
    rw [hw]
    change ((BitVec.ofNat 64 19 * BitVec.ofNat 64 (a i)).setWidth 32).setWidth 64 = _
    rw [← BitVec.ofNat_mul, BitVec.setWidth_ofNat_of_le (by decide)]
    exact BitVec.setWidth_ofNat_of_le_of_lt (w := 32) (v := 64) (by decide) (input_times19_lt_u32 ha i)

/-- All ten word expressions equal the integer polynomial cast to u64. -/
theorem machineColumns_ofNat {a : Limbs} (ha : Bounded a) (i : Fin 10) :
    machineColumns (fun j => BitVec.ofNat 32 (a j)) i = BitVec.ofNat 64 (columns a i) := by
  have hw (j : Fin 10) := (input_operations_exact ha j).1
  have hd (j : Fin 10) := (input_operations_exact ha j).2.1
  have hm (j : Fin 10) := (input_operations_exact ha j).2.2
  fin_cases i <;> dsimp [machineColumns]
  all_goals simp only [mul32, hw, hd, hm, ← BitVec.ofNat_mul, ← BitVec.ofNat_add,
    shift_one_ofNat]
  all_goals congr 1 <;> norm_num [columns] <;> ring

/-- No 64-bit convolution result wraps. -/
theorem machineColumns_toNat {a : Limbs} (ha : Bounded a) (i : Fin 10) :
    (machineColumns (fun j => BitVec.ofNat 32 (a j)) i).toNat = columns a i := by
  rw [machineColumns_ofNat ha, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  exact lt_trans (columns_lt_u63 ha i) (by norm_num)

/-- The word-level D-lane subtraction and blend before reduce64. -/
def machineSignedColumns (a : Raw) (negate : Bool) (i : Fin 10) : BitVec 64 :=
  if negate then BitVec.ofNat 64 (negateConstant i) - machineColumns a i
  else machineColumns a i

theorem machineSignedColumns_toNat {a : Limbs} (ha : Bounded a)
    (negate : Bool) (i : Fin 10) :
    (machineSignedColumns (fun j => BitVec.ofNat 32 (a j)) negate i).toNat =
      signedColumns a negate i := by
  cases negate
  · exact machineColumns_toNat ha i
  · have hk : (BitVec.ofNat 64 (negateConstant i)).toNat = negateConstant i := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      exact lt_trans (negateConstant_lt_u63 i) (by norm_num)
    have hb : machineColumns (fun j => BitVec.ofNat 32 (a j)) i ≤
        BitVec.ofNat 64 (negateConstant i) := by
      rw [BitVec.le_def, machineColumns_toNat ha i, hk]
      exact Nat.le_of_lt (columns_lt_negateConstant ha i)
    change (BitVec.ofNat 64 (negateConstant i) -
      machineColumns (fun j => BitVec.ofNat 32 (a j)) i).toNat =
        negateConstant i - columns a i
    rw [BitVec.toNat_sub_of_le hb, hk, machineColumns_toNat ha i]

end
end Agave.Ed25519.Avx2SquareNegateD

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.SLLVM.Tactic

/-!
# Lane-level semantics lemmas for LLVM vector operations

Rewrite rules that evaluate the vector operations of the LLVM dialect at the
level of individual values, without ever unfolding the dependently-typed
definitions (`dense`, `poison`, …) inside a goal — unfolding those forces
`whnf` to evaluate `Vector.ofFn` on symbolic lanes, which blows up.
-/

namespace Firedancer.R43x6
open LeanMLIR SLLVM
open InstCombine (LLVM)

namespace Lane
open InstCombine.LLVM.Ty
open LLVM (IntW)

variable {e : LLVM.Ty} {l w : Nat}

/-! ## Vector-level normal forms for the dependently-typed constants -/

theorem dense_vector_splat (v : Int) :
    dense (LLVM.Ty.vector l e) [v] = Vector.ofFn (fun _ : Fin l => dense e [v]) := rfl

theorem dense_vector_cons₂ (v₀ v₁ : Int) (rest : List Int) :
    dense (LLVM.Ty.vector l e) (v₀ :: v₁ :: rest)
      = Vector.ofFn (fun i : Fin l => dense e [(v₀ :: v₁ :: rest).getD i.val 0]) := rfl

theorem poison_vector :
    poison (LLVM.Ty.vector l e) = Vector.replicate l (poison e) := rfl

theorem poison_bitvec : poison (LLVM.Ty.bitvec w) = (PoisonOr.poison : IntW w) := rfl

theorem dense_bitvec (vals : List Int) :
    dense (LLVM.Ty.bitvec w) vals = .value (BitVec.ofInt w (vals.headD 0)) := rfl

/-! ## Value-level reductions of the vector/scalar operations -/

theorem vpmadd52Lane_value (hi : Bool) (a b c : BitVec 64) :
    vpmadd52Lane hi (.value a) (.value b) (.value c) =
      .value (a + BitVec.ofNat 64
        (if hi then (b.toNat % 2^52) * (c.toNat % 2^52) / 2^52
         else (b.toNat % 2^52) * (c.toNat % 2^52) % 2^52)) := rfl

/-- `vpmadd52luq` on values, with the branch on `hi` already taken. -/
theorem vpmadd52Lane_lo_value (a b c : BitVec 64) :
    vpmadd52Lane false (.value a) (.value b) (.value c) =
      .value (a + BitVec.ofNat 64 ((b.toNat % 2^52) * (c.toNat % 2^52) % 2^52)) := rfl

/-- `vpmadd52huq` on values, with the branch on `hi` already taken. -/
theorem vpmadd52Lane_hi_value (a b c : BitVec 64) :
    vpmadd52Lane true (.value a) (.value b) (.value c) =
      .value (a + BitVec.ofNat 64 ((b.toNat % 2^52) * (c.toNat % 2^52) / 2^52)) := rfl

theorem insertelement_value (v : Vector (TyDenote.toType e) l) (x : TyDenote.toType e)
    (c : BitVec w) :
    insertelement v x (.value c) =
      if h : c.toNat < l then v.set c.toNat x else Vector.replicate l (poison e) := rfl

theorem insertelement_poison (v : Vector (TyDenote.toType e) l) (x : TyDenote.toType e) :
    insertelement v x (PoisonOr.poison : IntW w) = Vector.replicate l (poison e) := rfl

theorem and_value (a b : BitVec w) :
    LLVM.and (.value a) (.value b) = .value (a &&& b) := rfl

theorem add_value (a b : BitVec w) :
    LLVM.add (.value a) (.value b) ⟨false, false⟩ = .value (a + b) := rfl

theorem add_poison_left (b : LLVM.IntW w) (f : LLVM.NoWrapFlags) :
    LLVM.add .poison b f = .poison := rfl

theorem add_poison_right (a : LLVM.IntW w) (f : LLVM.NoWrapFlags) :
    LLVM.add a .poison f = .poison := by
    unfold LLVM.add
    simp



theorem mul_value (a b : BitVec w) :
    LLVM.mul (.value a) (.value b) ⟨false, false⟩ = .value (a * b) := rfl

theorem shl_value64 (a b : BitVec 64) (h : b.toNat < 64) :
    LLVM.shl (.value a) (.value b) ⟨false, false⟩ = .value (a <<< b.toNat) := by
  have hge : ¬ (64#64 ≤ b) := by
    intro hc
    rw [BitVec.le_def, BitVec.toNat_ofNat] at hc
    omega
  simp [LLVM.shl, LLVM.shl?, hge]

/-! ## The specific constants `fd_r43x6_mul_fast` uses -/

theorem const?_eq (v : Int) : LLVM.const? w v = .value (BitVec.ofInt w v) := rfl

theorem shl_value_nine (a : BitVec 64) :
    LLVM.shl (.value a) (.value (BitVec.ofInt 64 9)) ⟨false, false⟩
      = .value (a <<< (9 : ℕ)) := by
  have h9 : (BitVec.ofInt 64 9).toNat = 9 := by decide
  rw [shl_value64 _ _ (by omega), h9]

theorem shl_value_seven (a : BitVec 64) :
    LLVM.shl (.value a) (.value (BitVec.ofInt 64 7)) ⟨false, false⟩
      = .value (a <<< (7 : ℕ)) := by
  have h7 : (BitVec.ofInt 64 7).toNat = 7 := by decide
  rw [shl_value64 _ _ (by omega), h7]

theorem mul_value_twentyfour (a : BitVec 64) :
    LLVM.mul (.value a) (.value (BitVec.ofInt 64 24)) ⟨false, false⟩
      = .value (a * 24#64) := rfl

theorem and_value_neg_one (a : BitVec 64) :
    LLVM.and (.value a) (.value (BitVec.ofInt 64 (-1))) = .value a := by
  rw [and_value]
  congr 1
  have : BitVec.ofInt 64 (-1) = BitVec.allOnes 64 := rfl
  rw [this, BitVec.and_allOnes]

theorem and_value_zero (a : BitVec 64) :
    LLVM.and (.value a) (.value (BitVec.ofInt 64 0)) = .value 0 := by
  rw [and_value]
  congr 1
  have : BitVec.ofInt 64 0 = 0#64 := rfl
  rw [this, BitVec.and_zero]
  rfl

theorem ofInt_zero_add (a : BitVec 64) : BitVec.ofInt 64 0 + a = a := by
  have : BitVec.ofInt 64 0 = 0#64 := rfl
  rw [this, BitVec.zero_add]

/-- BitVec-level version of the `-1` mask lane, so it applies after the
generic `and_value`. -/
theorem bv_and_ofInt_neg_one (a : BitVec 64) : a &&& BitVec.ofInt 64 (-1) = a := by
  have : BitVec.ofInt 64 (-1) = BitVec.allOnes 64 := rfl
  rw [this, BitVec.and_allOnes]

/-- BitVec-level version of the `0` mask lane. -/
theorem bv_and_ofInt_zero (a : BitVec 64) : a &&& BitVec.ofInt 64 0 = 0#64 := by
  have : BitVec.ofInt 64 0 = 0#64 := rfl
  rw [this, BitVec.and_zero]

/-! ## `toNat` computations for the endgame -/

theorem toNat_ofInt_24 : (BitVec.ofInt 64 24).toNat = 24 := by decide

theorem toNat_zero_64 : (0#64 : BitVec 64).toNat = 0 := rfl

theorem toNat_ofInt_zero : (BitVec.ofInt 64 0).toNat = 0 := rfl

theorem toNat_zero_lit : ((0 : BitVec 64)).toNat = 0 := rfl

theorem add_ofInt_zero (a : BitVec 64) : a + BitVec.ofInt 64 0 = a := by
  have : BitVec.ofInt 64 0 = 0#64 := rfl
  rw [this, BitVec.add_zero]

end Lane
end Firedancer.R43x6

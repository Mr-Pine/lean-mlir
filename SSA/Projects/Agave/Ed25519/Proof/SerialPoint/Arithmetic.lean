import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Algebra
import Mathlib.Data.ZMod.Basic

/-!
Arithmetic used by the compiler-extracted serial point kernels. Weak reduction
is the parallel carry schedule of `FieldElement51::reduce`, distinct from the
sequential multiplication carry schedule. Bounds concern concrete coefficients,
not a postulated field-operation contract.
-/
namespace Agave.Ed25519.SerialPoint
open SerialFieldMul
section

/-- Caller invariant at point-operation boundaries. -/
def Tight (a : Limbs) : Prop := ∀ i, a i < 2^52

def add (a b : Limbs) : Limbs := fun i => a i + b i

/-- The exact parallel 51-bit carry schedule in the Rust subtraction helper. -/
def weakReduce (a : Limbs) : Limbs := ![
  a 0 % radix + 19*(a 4 / radix),
  a 1 % radix + a 0 / radix,
  a 2 % radix + a 1 / radix,
  a 3 % radix + a 2 / radix,
  a 4 % radix + a 3 / radix]

def bias : Limbs := ![36028797018963664, 36028797018963952,
  36028797018963952, 36028797018963952, 36028797018963952]

def biasedSub (a b : Limbs) : Limbs := fun i => a i + bias i - b i

def sub (a b : Limbs) : Limbs := weakReduce (biasedSub a b)

def value (a : Limbs) : ZMod modulus := decode a

@[simp] theorem add_value (a b : Limbs) : value (add a b) = value a + value b := by
  simp only [value, decode, add, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  ring

theorem weakReduce_identity (a : Limbs) :
    decode (weakReduce a) + modulus * (a 4 / radix) = decode a := by
  have h0 := Nat.mod_add_div (a 0) radix
  have h1 := Nat.mod_add_div (a 1) radix
  have h2 := Nat.mod_add_div (a 2) radix
  have h3 := Nat.mod_add_div (a 3) radix
  have h4 := Nat.mod_add_div (a 4) radix
  norm_num [decode, weakReduce, radix, modulus] at *
  omega

@[simp] theorem weakReduce_value (a : Limbs) : value (weakReduce a) = value a := by
  have h := congrArg (fun n : Nat => (n : ZMod modulus)) (weakReduce_identity a)
  simpa [value, Nat.cast_add, Nat.cast_mul] using h

/-- Even completely arbitrary 64-bit inputs weak-reduce below 2^52. -/
theorem weakReduce_tight (a : Limbs) (ha : ∀ i, a i < 2^64) : Tight (weakReduce a) := by
  have hlo (i : Fin 5) := Nat.mod_lt (a i) (by decide : 0 < radix)
  have hhi (i : Fin 5) : a i / radix < 2^13 := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < radix)).2
    have := ha i
    norm_num [radix] at *
    omega
  intro i
  fin_cases i <;> simp [weakReduce]
  all_goals
    have h0 := hlo 0; have h1 := hlo 1; have h2 := hlo 2
    have h3 := hlo 3; have h4 := hlo 4
    have c0 := hhi 0; have c1 := hhi 1; have c2 := hhi 2
    have c3 := hhi 3; have c4 := hhi 4
    norm_num [radix] at *
    omega

theorem bias_large (i : Fin 5) : 2^54 ≤ bias i := by fin_cases i <;> decide

theorem bias_small (i : Fin 5) : bias i < 2^55 := by fin_cases i <;> decide

/-- The bias is exactly 16p in radix 51. -/
theorem bias_decode : decode bias = 16*modulus := by decide

theorem biasedSub_add (a b : Limbs) (hb : Bounded b) (i : Fin 5) :
    biasedSub a b i + b i = a i + bias i := by
  apply Nat.sub_add_cancel
  have := hb i
  have := bias_large i
  omega

theorem biasedSub_identity (a b : Limbs) (hb : Bounded b) :
    decode (biasedSub a b) + decode b = decode a + 16*modulus := by
  have h0 := biasedSub_add a b hb 0
  have h1 := biasedSub_add a b hb 1
  have h2 := biasedSub_add a b hb 2
  have h3 := biasedSub_add a b hb 3
  have h4 := biasedSub_add a b hb 4
  norm_num [decode, bias, radix, modulus] at *
  omega

@[simp] theorem sub_value (a b : Limbs) (hb : Bounded b) :
    value (sub a b) = value a - value b := by
  have h := congrArg (fun n : Nat => (n : ZMod modulus)) (biasedSub_identity a b hb)
  have h' : value (biasedSub a b) + value b = value a := by
    simpa [value, Nat.cast_add, Nat.cast_mul] using h
  rw [sub, weakReduce_value]
  exact eq_sub_iff_add_eq.mpr h'

/-- All additions preceding a biased subtraction and all final outputs fit u64. -/
theorem sub_safe (a b : Limbs) (ha : Bounded a) (hb : Bounded b) :
    (∀ i, a i + bias i < 2^64) ∧
    (∀ i, b i ≤ a i + bias i) ∧ Tight (sub a b) := by
  have hsum (i : Fin 5) : a i + bias i < 2^64 := by
    have := ha i; have := bias_small i
    norm_num at *
    omega
  have hdiff (i : Fin 5) : biasedSub a b i < 2^64 := by
    have := hsum i
    unfold biasedSub
    omega
  refine ⟨hsum, ?_, weakReduce_tight _ hdiff⟩
  intro i
  have := hb i; have := bias_large i
  omega

theorem tight_bounded (a : Limbs) (ha : Tight a) : Bounded a := by
  intro i
  have := ha i
  norm_num at *
  omega

theorem add_bounded (a b : Limbs) (ha : Tight a) (hb : Tight b) : Bounded (add a b) := by
  intro i
  have := ha i; have := hb i
  simp only [add]
  norm_num at *
  omega

/-- Squaring uses symmetry to reduce products, but has exactly the same columns
as multiplication with equal inputs. This is not an assertion of code identity. -/
def squareColumns (a : Limbs) : Limbs := ![
  a 0*a 0 + 2*(a 1*(19*a 4) + a 2*(19*a 3)),
  a 3*(19*a 3) + 2*(a 0*a 1 + a 2*(19*a 4)),
  a 1*a 1 + 2*(a 0*a 2 + a 4*(19*a 3)),
  a 4*(19*a 4) + 2*(a 0*a 3 + a 1*a 2),
  a 2*a 2 + 2*(a 0*a 4 + a 1*a 3)]

theorem squareColumns_eq (a : Limbs) : squareColumns a = columns a a := by
  funext i
  fin_cases i <;> simp [squareColumns, columns] <;> ring

@[simp] theorem mul_value (a b : Limbs) :
    value (reduce (columns a b)) = value a * value b := by
  have h := congrArg (fun n : Nat => (n : ZMod modulus)) (reduce_identity (columns a b))
  have hc := congrArg (fun n : Nat => (n : ZMod modulus)) (columns_identity a b)
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero] at h hc
  exact h.trans hc

@[simp] theorem square_value (a : Limbs) :
    value (reduce (squareColumns a)) = value a ^ 2 := by
  rw [squareColumns_eq, mul_value, pow_two]

end
end Agave.Ed25519.SerialPoint

import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

/-!
# Ed25519 field representations

The physical SIMD layout is the layout of `FieldElement2625x4` in
`solana-ed25519` 0.2.4, `src/backend/vector/avx2/field.rs`. Each of the five
registers contains `(a_even, b_even, a_odd, b_odd, c_even, d_even, c_odd, d_odd)`.
This file specifies representations, not the correctness of extracted code.
In particular `split` below specifies the integer result of the Rust `split`
method; a separate RIR theorem must connect its instructions to this function.
-/

namespace Agave.Ed25519.Field

/-- The prime modulus of the Ed25519 base field. -/
def p : Nat := 2 ^ 255 - 19

/-- Five serial radix-51 coefficients, without a reduction premise. -/
abbrev Serial := Fin 5 → BitVec 64

/-- Five SIMD registers, each containing eight physical 32-bit lanes. -/
abbrev Packed := Fin 5 → Fin 8 → BitVec 32

/-- Four mathematical field elements, in the order A, B, C, D. -/
abbrev Element := Fin 4

/-- The physical lane carrying an even coefficient of each element. -/
def evenLane (e : Element) : Fin 8 := ![0, 1, 4, 5] e

/-- The physical lane carrying an odd coefficient of each element. -/
def oddLane (e : Element) : Fin 8 := ![2, 3, 6, 7] e

@[simp] theorem evenLane_A : evenLane 0 = 0 := rfl
@[simp] theorem evenLane_B : evenLane 1 = 1 := rfl
@[simp] theorem evenLane_C : evenLane 2 = 4 := rfl
@[simp] theorem evenLane_D : evenLane 3 = 5 := rfl
@[simp] theorem oddLane_A : oddLane 0 = 2 := rfl
@[simp] theorem oddLane_B : oddLane 1 = 3 := rfl
@[simp] theorem oddLane_C : oddLane 2 = 6 := rfl
@[simp] theorem oddLane_D : oddLane 3 = 7 := rfl

def lo (v : Packed) (e : Element) (i : Fin 5) : Nat :=
  (v i (evenLane e)).toNat

def hi (v : Packed) (e : Element) (i : Fin 5) : Nat :=
  (v i (oddLane e)).toNat

/-- Integer decoding of five radix-51 coefficients. -/
def decode51 (x : Fin 5 → Nat) : Nat :=
  ∑ i : Fin 5, x i * 2 ^ (51 * i.val)

/-- Integer decoding of ten alternating 26/25-bit coefficients.
No coefficient bound is needed to define or compare these integers. -/
def decode2625 (low high : Fin 5 → Nat) : Nat :=
  ∑ i : Fin 5,
    (low i * 2 ^ (51 * i.val) + high i * 2 ^ (51 * i.val + 26))

/-- Bit position of a coefficient in the alternating radix-26/25 format. -/
def exponent (i : Fin 10) : Nat := 51 * (i.val / 2) + 26 * (i.val % 2)

def decode10 (x : Fin 10 → Nat) : Nat := ∑ i, x i * 2 ^ exponent i

/-- Interleave the even and odd coefficients into their mathematical order. -/
def flatten (low high : Fin 5 → Nat) (i : Fin 10) : Nat :=
  let j : Fin 5 := ⟨i.val / 2, by omega⟩
  if i.val % 2 = 0 then low j else high j

theorem decode_flatten (low high : Fin 5 → Nat) :
    decode10 (flatten low high) = decode2625 low high := by
  simp [decode10, decode2625, flatten, exponent, Fin.sum_univ_succ]
  ring

def serialValue (x : Serial) : Nat := decode51 (fun i => (x i).toNat)

def packedValue (v : Packed) (e : Element) : Nat :=
  decode2625 (lo v e) (hi v e)

/-- Pair adjacent radix-26/25 coefficients into radix-51 coefficients. -/
def pair (low high : Fin 5 → Nat) (i : Fin 5) : Nat :=
  low i + high i * 2 ^ 26

/-- Pairing is integer equality, even for arbitrarily large coefficients. -/
theorem decode_pair (low high : Fin 5 → Nat) :
    decode51 (pair low high) = decode2625 low high := by
  unfold decode51 decode2625 pair
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_add]
  ring

/-- Every pair of u32 coefficients fits in u64 after shifting the odd one
by 26. This discharges the entire overflow premise for Rust `split`. -/
theorem pair_u32_lt_u64 (low high : BitVec 32) :
    low.toNat + high.toNat * 2 ^ 26 < 2 ^ 64 := by
  have hl := low.isLt
  have hh := high.isLt
  norm_num at hl hh ⊢
  omega

/-- Mathematical specification of the serial limbs returned by `split`. -/
def split (v : Packed) (e : Element) : Serial := fun i =>
  BitVec.ofNat 64 (pair (lo v e) (hi v e) i)

@[simp] theorem split_toNat (v : Packed) (e : Element) (i : Fin 5) :
    (split v e i).toNat = pair (lo v e) (hi v e) i := by
  simp only [split, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  exact pair_u32_lt_u64 (v i (evenLane e)) (v i (oddLane e))

/-- Unconditional value preservation for all forty physical u32 lanes. -/
theorem split_value (v : Packed) (e : Element) :
    serialValue (split v e) = packedValue v e := by
  simp only [serialValue, split_toNat, packedValue]
  exact decode_pair (lo v e) (hi v e)

/-- Canonical radix-51 limb bounds; this is not canonical field encoding. -/
def Tight51 (x : Fin 5 → Nat) : Prop := ∀ i, x i < 2 ^ 51

/-- Exact integer upper bounds established by the one-pass `reduce` routine
on arbitrary u32 inputs. The exceptional low limb receives 19 times a carry. -/
def Reduced2625 (low high : Fin 5 → Nat) : Prop :=
  (∀ i, low i ≤ 2 ^ 26 - 1 + (if i = 0 then 19 * 127 else 127)) ∧
  (∀ i, high i ≤ 2 ^ 25 - 1 + 63)

/-- A convenient integer slack invariant for subsequent field operations. -/
def Loose2625 (low high : Fin 5 → Nat) : Prop :=
  (∀ i, low i < 2 ^ 26 + 2 ^ 18) ∧
  (∀ i, high i < 2 ^ 25 + 2 ^ 18)

/-- The documented b=1 input bound for multiplication. -/
def MulBound (x : Fin 10 → Nat) : Prop :=
  ∀ i, x i < 2 ^ (if i.val % 2 = 0 then 27 else 26)

theorem loose_mulBound {low high : Fin 5 → Nat}
    (h : Loose2625 low high) : MulBound (flatten low high) := by
  intro i
  unfold flatten
  split_ifs with he
  · have hl := h.1 ⟨i.val / 2, by omega⟩
    norm_num at hl ⊢
    omega
  · have hh := h.2 ⟨i.val / 2, by omega⟩
    norm_num at hh ⊢
    omega

theorem reduced_loose {low high : Fin 5 → Nat}
    (h : Reduced2625 low high) : Loose2625 low high := by
  constructor
  · intro i
    have hl := h.1 i
    split_ifs at hl <;> norm_num at hl ⊢ <;> omega
  · intro i
    have hh := h.2 i
    norm_num at hh ⊢
    omega

/-- Field equality is equality after reduction of the represented integers. -/
def SameField (x y : Nat) : Prop := x % p = y % p

theorem p_pos : 0 < p := by norm_num [p]

theorem two_pow_255 : 2 ^ 255 = p + 19 := by norm_num [p]

theorem sameField_refl (x : Nat) : SameField x x := rfl

theorem sameField_symm {x y : Nat} (h : SameField x y) : SameField y x := h.symm

theorem sameField_trans {x y z : Nat} (hxy : SameField x y)
    (hyz : SameField y z) : SameField x z := hxy.trans hyz

theorem sameField_add {a b c d : Nat} (hab : SameField a b)
    (hcd : SameField c d) : SameField (a + c) (b + d) := by
  unfold SameField at *
  rw [Nat.add_mod a c, Nat.add_mod b d, hab, hcd]

theorem sameField_mul {a b c d : Nat} (hab : SameField a b)
    (hcd : SameField c d) : SameField (a * c) (b * d) := by
  unfold SameField at *
  rw [Nat.mul_mod a c, Nat.mul_mod b d, hab, hcd]

/-- The wraparound carry used by reduction is valid for any carry size. -/
theorem fold255 (x carry : Nat) :
    SameField (x + carry * 2 ^ 255) (x + carry * 19) := by
  unfold SameField
  rw [two_pow_255, Nat.mul_add]
  have he : x + (carry * p + carry * 19) = (x + carry * 19) + carry * p := by omega
  rw [he, Nat.add_mul_mod_self_right]

theorem split_sameField (v : Packed) (e : Element) :
    SameField (serialValue (split v e)) (packedValue v e) := by
  rw [split_value]
  exact sameField_refl _

end Agave.Ed25519.Field

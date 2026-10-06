module

public import Mathlib.Tactic

/-!
Radix-51 arithmetic for the pinned `solana-ed25519` 0.2.4 serial multiplication.
The carry identities are unconditional over natural numbers. The separate bounds
match the source's documented caller invariant, each limb strictly below `2^54`.
This file does not assert a connection to machine execution.
-/

namespace Agave.Ed25519.SerialFieldMul
@[expose] public section

abbrev Limbs := Fin 5 → Nat
abbrev radix : Nat := 2^51
abbrev modulus : Nat := 2^255 - 19

def decode (a : Limbs) : Nat :=
  a 0 + radix*a 1 + radix^2*a 2 + radix^3*a 3 + radix^4*a 4

/-- The five convolution columns, with `2^255` folded to 19. -/
def columns (a b : Limbs) : Limbs := ![
  a 0*b 0 + 19*(a 4*b 1 + a 3*b 2 + a 2*b 3 + a 1*b 4),
  a 1*b 0 + a 0*b 1 + 19*(a 4*b 2 + a 3*b 3 + a 2*b 4),
  a 2*b 0 + a 1*b 1 + a 0*b 2 + 19*(a 4*b 3 + a 3*b 4),
  a 3*b 0 + a 2*b 1 + a 1*b 2 + a 0*b 3 + 19*(a 4*b 4),
  a 4*b 0 + a 3*b 1 + a 2*b 2 + a 1*b 3 + a 0*b 4]

/-- Sequential wide columns, including the preceding carry. -/
def carried (c : Limbs) : Limbs :=
  let t0 := c 0
  let t1 := c 1 + t0 / radix
  let t2 := c 2 + t1 / radix
  let t3 := c 3 + t2 / radix
  let t4 := c 4 + t3 / radix
  ![t0,t1,t2,t3,t4]

def folded (c : Limbs) : Nat := c 0 % radix + 19*(carried c 4 / radix)

/-- Output of the source's carry schedule, before machine-word truncation. -/
def reduce (c : Limbs) : Limbs := ![
  folded c % radix,
  carried c 1 % radix + folded c / radix,
  carried c 2 % radix,
  carried c 3 % radix,
  carried c 4 % radix]

/-- The exact integer identity behind the reduction; no bounds are required. -/
theorem reduce_identity (c : Limbs) :
    decode (reduce c) + modulus * (carried c 4 / radix) = decode c := by
  have h0 := Nat.mod_add_div (c 0) radix
  have h1 := Nat.mod_add_div (carried c 1) radix
  have h2 := Nat.mod_add_div (carried c 2) radix
  have h3 := Nat.mod_add_div (carried c 3) radix
  have h4 := Nat.mod_add_div (carried c 4) radix
  have hf := Nat.mod_add_div (folded c) radix
  norm_num [decode, reduce, folded, carried, radix, modulus] at *
  omega

/-- The high-degree terms removed by the cyclic convolution. -/
def high (a b : Limbs) : Nat :=
  a 4*b 1 + a 3*b 2 + a 2*b 3 + a 1*b 4 +
  radix*(a 4*b 2 + a 3*b 3 + a 2*b 4) +
  radix^2*(a 4*b 3 + a 3*b 4) + radix^3*(a 4*b 4)

theorem columns_identity (a b : Limbs) :
    decode (columns a b) + modulus * high a b = decode a * decode b := by
  norm_num [decode, columns, high, radix, modulus]
  ring

/-- Field multiplication correctness of the unbounded carry schedule. -/
theorem reduce_columns_mod (a b : Limbs) :
    decode (reduce (columns a b)) % modulus = (decode a * decode b) % modulus := by
  have h := reduce_identity (columns a b)
  have hc := columns_identity a b
  calc
    _ = (decode (reduce (columns a b)) + modulus * (carried (columns a b) 4 / radix)) % modulus := by simp [Nat.add_mod]
    _ = decode (columns a b) % modulus := congrArg (· % modulus) h
    _ = (decode (columns a b) + modulus * high a b) % modulus := by simp [Nat.add_mod]
    _ = _ := congrArg (· % modulus) hc

/-- Four output limbs are fully reduced, even without input bounds. -/
theorem reduce_bounds (c : Limbs) :
    reduce c 0 < radix ∧ reduce c 2 < radix ∧
    reduce c 3 < radix ∧ reduce c 4 < radix := by
  simp only [reduce, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.cons_val_three]
  exact ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
    Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩

/-- The caller invariant stated by the Rust kernel. -/
def Bounded (a : Limbs) : Prop := ∀ i, a i < 2^54

/-- All carried wide columns fit the 115 bits whose upper 64 bits are retained by Rust. -/
theorem carried_bounds (a b : Limbs) (ha : Bounded a) (hb : Bounded b) :
    (∀ i, carried (columns a b) i < 2^115) ∧ folded (columns a b) < 2^64 := by
  have hm (i j : Fin 5) : a i * b j < 2^108 := by
    have h := Nat.mul_lt_mul_of_lt_of_lt (ha i) (hb j)
    norm_num at h ⊢
    exact h
  have h00 := hm 0 0; have h01 := hm 0 1; have h02 := hm 0 2
  have h03 := hm 0 3; have h04 := hm 0 4
  have h10 := hm 1 0; have h11 := hm 1 1; have h12 := hm 1 2
  have h13 := hm 1 3; have h14 := hm 1 4
  have h20 := hm 2 0; have h21 := hm 2 1; have h22 := hm 2 2
  have h23 := hm 2 3; have h24 := hm 2 4
  have h30 := hm 3 0; have h31 := hm 3 1; have h32 := hm 3 2
  have h33 := hm 3 3; have h34 := hm 3 4
  have h40 := hm 4 0; have h41 := hm 4 1; have h42 := hm 4 2
  have h43 := hm 4 3; have h44 := hm 4 4
  constructor
  · intro i
    fin_cases i <;> norm_num [carried, columns, radix] <;> omega
  · norm_num [folded, carried, columns, radix]
    omega

/-- Output bounds required by subsequent serial operations. Limb 1 has at most
13 extra low carry bits; the other four limbs are below `2^51`. -/
theorem mul_output_bounds (a b : Limbs) (ha : Bounded a) (hb : Bounded b) :
    (∀ i, i ≠ 1 → reduce (columns a b) i < radix) ∧
    reduce (columns a b) 1 < radix + 2^13 ∧
    Bounded (reduce (columns a b)) := by
  have hfour := reduce_bounds (columns a b)
  have hfold := (carried_bounds a b ha hb).2
  have hrem := Nat.mod_lt (carried (columns a b) 1) (show 0 < radix by decide)
  have hone : reduce (columns a b) 1 < radix + 2^13 := by
    simp only [reduce, Matrix.cons_val_one]
    norm_num [radix] at *
    omega
  have hrest : ∀ i : Fin 5, i ≠ 1 → reduce (columns a b) i < radix := by
    intro i hi
    fin_cases i <;> simp_all
  refine ⟨hrest, hone, ?_⟩
  intro i
  by_cases hi : i = 1
  · subst i; norm_num [radix] at hone ⊢; omega
  · have h := hrest i hi; norm_num [radix] at h ⊢; omega

end
end Agave.Ed25519.SerialFieldMul

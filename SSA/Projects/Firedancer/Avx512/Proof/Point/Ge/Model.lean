/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_quad_sqr_fast
public import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_quad_mul_fast
public import SSA.Projects.Firedancer.Avx512.Proof.Quad

/-!
# The `FD_R43X6_GE` macros' shared model

`FD_R43X6_QUAD_FOLD_SIGNED` as a function on QUADs (`foldSignedQuad`), the signed
limbs of a QUAD (`quadInt`) and what the fold does to them, and the bridges from
limbs to field elements the point proofs read their results through.
-/

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

namespace Ge

/-- The signed fold's limb-0 lane: `x` limb 0, `y` limb 5. -/
def fsL0 (x y : BitVec 64) : BitVec 64 :=
  ((x + 18446744073550168064#64) &&& 8796093022207#64) + 159383552#64
    + (y + 18446744073708503040#64).sshiftRight 40 * 19#64

/-- ... limb 3: `x` limb 3, `y` limb 2. -/
def fsL3 (x y : BitVec 64) : BitVec 64 :=
  ((x + 18446744073708503040#64) &&& 8796093022207#64) + 1048576#64
    + (y + 18446744073708503040#64).sshiftRight 43

/-- ... limbs 1, 2, 4, 5: `x` the limb below (biased by `nb`), `y` the limb,
`m` its mask. -/
def fsMid (x nb y m : BitVec 64) : BitVec 64 :=
  ((x + nb).sshiftRight 43 + 1048576#64) + ((y + 18446744073708503040#64) &&& m)

/-- `FD_R43X6_QUAD_FOLD_SIGNED`. -/
def foldSignedQuad (q : Quad) : Quad where
  v03 := #v[fsL0 q.v03[0] q.v25[4], fsL0 q.v03[1] q.v25[5], fsL0 q.v03[2] q.v25[6],
    fsL0 q.v03[3] q.v25[7], fsL3 q.v03[4] q.v25[0], fsL3 q.v03[5] q.v25[1],
    fsL3 q.v03[6] q.v25[2], fsL3 q.v03[7] q.v25[3]]
  v14 := #v[fsMid q.v03[0] 18446744073550168064#64 q.v14[0] 8796093022207#64,
    fsMid q.v03[1] 18446744073550168064#64 q.v14[1] 8796093022207#64,
    fsMid q.v03[2] 18446744073550168064#64 q.v14[2] 8796093022207#64,
    fsMid q.v03[3] 18446744073550168064#64 q.v14[3] 8796093022207#64,
    fsMid q.v03[4] 18446744073708503040#64 q.v14[4] 8796093022207#64,
    fsMid q.v03[5] 18446744073708503040#64 q.v14[5] 8796093022207#64,
    fsMid q.v03[6] 18446744073708503040#64 q.v14[6] 8796093022207#64,
    fsMid q.v03[7] 18446744073708503040#64 q.v14[7] 8796093022207#64]
  v25 := #v[fsMid q.v14[0] 18446744073708503040#64 q.v25[0] 8796093022207#64,
    fsMid q.v14[1] 18446744073708503040#64 q.v25[1] 8796093022207#64,
    fsMid q.v14[2] 18446744073708503040#64 q.v25[2] 8796093022207#64,
    fsMid q.v14[3] 18446744073708503040#64 q.v25[3] 8796093022207#64,
    fsMid q.v14[4] 18446744073708503040#64 q.v25[4] 1099511627775#64,
    fsMid q.v14[5] 18446744073708503040#64 q.v25[5] 1099511627775#64,
    fsMid q.v14[6] 18446744073708503040#64 q.v25[6] 1099511627775#64,
    fsMid q.v14[7] 18446744073708503040#64 q.v25[7] 1099511627775#64]

/-! ## One lane at a time, over `ℤ` -/

section Lanes
open R43x6 (FitsLong)

private theorem toInt_add_ofInt {x : BitVec 64} {c : ℤ} (h : FitsLong (x.toInt + c)) :
    (x + BitVec.ofInt 64 c).toInt = x.toInt + c := by
  rw [← toInt_ofInt h, BitVec.ofInt_add, ofInt_toInt]

private theorem ofNat_eq_ofInt (n : ℕ) : BitVec.ofNat 64 n = BitVec.ofInt 64 (n : ℤ) := by
  apply BitVec.eq_of_toNat_eq; simp

private theorem ofInt_sub64 (a b : ℤ) :
    BitVec.ofInt 64 a - BitVec.ofInt 64 b = BitVec.ofInt 64 (a - b) := by
  apply BitVec.eq_of_toInt_eq
  simp [BitVec.toInt_sub, BitVec.toInt_ofInt, Int.sub_emod, Int.bmod]
  omega

/-- `G`'s lane: `a - b + k`. -/
theorem toInt_laneG {a b k : ℕ} (ha : a < 2 ^ 61) (hb : b < 2 ^ 61) (hk : k < 2 ^ 44) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b + BitVec.ofNat 64 k).toInt = (a : ℤ) - b + k := by
  rw [ofNat_eq_ofInt a, ofNat_eq_ofInt b, ofNat_eq_ofInt k, ofInt_sub64, ← BitVec.ofInt_add,
    toInt_ofInt]
  simp only [FitsLong]; omega

/-- `H`'s lane: `a + b`. -/
theorem toInt_laneH {a b : ℕ} (ha : a < 2 ^ 61) (hb : b < 2 ^ 61) :
    (BitVec.ofNat 64 a + BitVec.ofNat 64 b).toInt = (a : ℤ) + b := by
  rw [ofNat_eq_ofInt a, ofNat_eq_ofInt b, ← BitVec.ofInt_add, toInt_ofInt]
  simp only [FitsLong]; omega

/-- The signed fold's input range: what `(E, G, F, H)` occupy, with room for
the bias. -/
abbrev InFold (x : ℤ) : Prop := -2 ^ 62 ≤ x ∧ x < 2 ^ 63 - 2 ^ 29

private theorem ofInt_nb0 :
    (18446744073550168064#64 : BitVec 64) = BitVec.ofInt 64 (-159383552) := rfl
private theorem ofInt_nb : (18446744073708503040#64 : BitVec 64) = BitVec.ofInt 64 (-1048576) := rfl

theorem toInt_fsL0 {x y : BitVec 64} (hx : InFold x.toInt) (hy : InFold y.toInt) :
    (fsL0 x y).toInt
      = (x.toInt - 19 * 2 ^ 23) % 2 ^ 43 + 19 * ((y.toInt - 2 ^ 20) / 2 ^ 40) + 19 * 2 ^ 23 := by
  have e1 : (x + 18446744073550168064#64).toInt = x.toInt - 159383552 := by
    rw [ofInt_nb0, toInt_add_ofInt (by simp only [FitsLong]; omega)]; ring
  have e2 : (y + 18446744073708503040#64).toInt = y.toInt - 1048576 := by
    rw [ofInt_nb, toInt_add_ofInt (by simp only [FitsLong]; omega)]; ring
  have hm := Int.emod_nonneg (x.toInt - 159383552) (by norm_num : (2 : ℤ) ^ 43 ≠ 0)
  have hm' := Int.emod_lt_of_pos (x.toInt - 159383552) (by norm_num : (0 : ℤ) < 2 ^ 43)
  have hd1 : -2 ^ 23 - 1 ≤ (y.toInt - 1048576) / 2 ^ 40 := by
    apply Int.le_ediv_of_mul_le (by norm_num); omega
  have hd2 : (y.toInt - 1048576) / 2 ^ 40 < 2 ^ 23 := by
    apply Int.ediv_lt_of_lt_mul (by norm_num); omega
  simp only [fsL0]
  rw [and_mask43_int, sshiftRight_ofInt, e1, e2, R43x6.shiftRight_eq,
    show (159383552#64 : BitVec 64) = BitVec.ofInt 64 159383552 from rfl,
    show (19#64 : BitVec 64) = BitVec.ofInt 64 19 from rfl,
    ← BitVec.ofInt_add, ← BitVec.ofInt_mul, ← BitVec.ofInt_add, toInt_ofInt]
  · push_cast; ring_nf
  · simp only [FitsLong]; constructor <;> push_cast <;> omega

theorem toInt_fsL3 {x y : BitVec 64} (hx : InFold x.toInt) (hy : InFold y.toInt) :
    (fsL3 x y).toInt = (x.toInt - 2 ^ 20) % 2 ^ 43 + (y.toInt - 2 ^ 20) / 2 ^ 43 + 2 ^ 20 := by
  have e1 : (x + 18446744073708503040#64).toInt = x.toInt - 1048576 := by
    rw [ofInt_nb, toInt_add_ofInt (by simp only [FitsLong]; omega)]; ring
  have e2 : (y + 18446744073708503040#64).toInt = y.toInt - 1048576 := by
    rw [ofInt_nb, toInt_add_ofInt (by simp only [FitsLong]; omega)]; ring
  have hm := Int.emod_nonneg (x.toInt - 1048576) (by norm_num : (2 : ℤ) ^ 43 ≠ 0)
  have hm' := Int.emod_lt_of_pos (x.toInt - 1048576) (by norm_num : (0 : ℤ) < 2 ^ 43)
  have hd1 : -2 ^ 20 - 1 ≤ (y.toInt - 1048576) / 2 ^ 43 := by
    apply Int.le_ediv_of_mul_le (by norm_num); omega
  have hd2 : (y.toInt - 1048576) / 2 ^ 43 < 2 ^ 20 := by
    apply Int.ediv_lt_of_lt_mul (by norm_num); omega
  simp only [fsL3]
  rw [and_mask43_int, sshiftRight_ofInt, e1, e2, R43x6.shiftRight_eq,
    show (1048576#64 : BitVec 64) = BitVec.ofInt 64 1048576 from rfl,
    ← BitVec.ofInt_add, ← BitVec.ofInt_add, toInt_ofInt]
  · push_cast; ring_nf
  · simp only [FitsLong]; constructor <;> push_cast <;> omega

/-- `fsMid` with the limb-0 bias below and a 43-bit mask: limb 1. -/
theorem toInt_fsMid_b0 {x y : BitVec 64} (hx : InFold x.toInt) (hy : InFold y.toInt) :
    (fsMid x 18446744073550168064#64 y 8796093022207#64).toInt
      = (y.toInt - 2 ^ 20) % 2 ^ 43 + (x.toInt - 19 * 2 ^ 23) / 2 ^ 43 + 2 ^ 20 := by
  have e1 : (x + 18446744073550168064#64).toInt = x.toInt - 159383552 := by
    rw [ofInt_nb0, toInt_add_ofInt (by simp only [FitsLong]; omega)]; ring
  have e2 : (y + 18446744073708503040#64).toInt = y.toInt - 1048576 := by
    rw [ofInt_nb, toInt_add_ofInt (by simp only [FitsLong]; omega)]; ring
  have hm := Int.emod_nonneg (y.toInt - 1048576) (by norm_num : (2 : ℤ) ^ 43 ≠ 0)
  have hm' := Int.emod_lt_of_pos (y.toInt - 1048576) (by norm_num : (0 : ℤ) < 2 ^ 43)
  have hd1 : -2 ^ 20 - 1 ≤ (x.toInt - 159383552) / 2 ^ 43 := by
    apply Int.le_ediv_of_mul_le (by norm_num); omega
  have hd2 : (x.toInt - 159383552) / 2 ^ 43 < 2 ^ 20 := by
    apply Int.ediv_lt_of_lt_mul (by norm_num); omega
  simp only [fsMid]
  rw [and_mask43_int, sshiftRight_ofInt, e1, e2, R43x6.shiftRight_eq,
    show (1048576#64 : BitVec 64) = BitVec.ofInt 64 1048576 from rfl,
    ← BitVec.ofInt_add, ← BitVec.ofInt_add, toInt_ofInt]
  · push_cast; ring_nf
  · simp only [FitsLong]; constructor <;> push_cast <;> omega

/-- `fsMid` with the `2^20` bias below and a 43-bit mask: limbs 2 and 4. -/
theorem toInt_fsMid_bb {x y : BitVec 64} (hx : InFold x.toInt) (hy : InFold y.toInt) :
    (fsMid x 18446744073708503040#64 y 8796093022207#64).toInt
      = (y.toInt - 2 ^ 20) % 2 ^ 43 + (x.toInt - 2 ^ 20) / 2 ^ 43 + 2 ^ 20 := by
  have e1 : (x + 18446744073708503040#64).toInt = x.toInt - 1048576 := by
    rw [ofInt_nb, toInt_add_ofInt (by simp only [FitsLong]; omega)]; ring
  have e2 : (y + 18446744073708503040#64).toInt = y.toInt - 1048576 := by
    rw [ofInt_nb, toInt_add_ofInt (by simp only [FitsLong]; omega)]; ring
  have hm := Int.emod_nonneg (y.toInt - 1048576) (by norm_num : (2 : ℤ) ^ 43 ≠ 0)
  have hm' := Int.emod_lt_of_pos (y.toInt - 1048576) (by norm_num : (0 : ℤ) < 2 ^ 43)
  have hd1 : -2 ^ 20 - 1 ≤ (x.toInt - 1048576) / 2 ^ 43 := by
    apply Int.le_ediv_of_mul_le (by norm_num); omega
  have hd2 : (x.toInt - 1048576) / 2 ^ 43 < 2 ^ 20 := by
    apply Int.ediv_lt_of_lt_mul (by norm_num); omega
  simp only [fsMid]
  rw [and_mask43_int, sshiftRight_ofInt, e1, e2, R43x6.shiftRight_eq,
    show (1048576#64 : BitVec 64) = BitVec.ofInt 64 1048576 from rfl,
    ← BitVec.ofInt_add, ← BitVec.ofInt_add, toInt_ofInt]
  · push_cast; ring_nf
  · simp only [FitsLong]; constructor <;> push_cast <;> omega

/-- `fsMid` with a 40-bit mask: limb 5. -/
theorem toInt_fsMid_m40 {x y : BitVec 64} (hx : InFold x.toInt) (hy : InFold y.toInt) :
    (fsMid x 18446744073708503040#64 y 1099511627775#64).toInt
      = (y.toInt - 2 ^ 20) % 2 ^ 40 + (x.toInt - 2 ^ 20) / 2 ^ 43 + 2 ^ 20 := by
  have e1 : (x + 18446744073708503040#64).toInt = x.toInt - 1048576 := by
    rw [ofInt_nb, toInt_add_ofInt (by simp only [FitsLong]; omega)]; ring
  have e2 : (y + 18446744073708503040#64).toInt = y.toInt - 1048576 := by
    rw [ofInt_nb, toInt_add_ofInt (by simp only [FitsLong]; omega)]; ring
  have hm := Int.emod_nonneg (y.toInt - 1048576) (by norm_num : (2 : ℤ) ^ 40 ≠ 0)
  have hm' := Int.emod_lt_of_pos (y.toInt - 1048576) (by norm_num : (0 : ℤ) < 2 ^ 40)
  have hd1 : -2 ^ 20 - 1 ≤ (x.toInt - 1048576) / 2 ^ 43 := by
    apply Int.le_ediv_of_mul_le (by norm_num); omega
  have hd2 : (x.toInt - 1048576) / 2 ^ 43 < 2 ^ 20 := by
    apply Int.ediv_lt_of_lt_mul (by norm_num); omega
  simp only [fsMid]
  rw [and_mask40_int, sshiftRight_ofInt, e1, e2, R43x6.shiftRight_eq,
    show (1048576#64 : BitVec 64) = BitVec.ofInt 64 1048576 from rfl,
    ← BitVec.ofInt_add, ← BitVec.ofInt_add, toInt_ofInt]
  · push_cast; ring_nf
  · simp only [FitsLong]; constructor <;> push_cast <;> omega

end Lanes

/-! ## Integer limbs of a QUAD -/

/-- `vlane`'s `ℤ` twin. -/
def vlaneInt (v : Vector (BitVec 64) 8) : Fin 8 → ℤ
  | 0 => v[0].toInt
  | 1 => v[1].toInt
  | 2 => v[2].toInt
  | 3 => v[3].toInt
  | 4 => v[4].toInt
  | 5 => v[5].toInt
  | 6 => v[6].toInt
  | 7 => v[7].toInt

/-- `quadLimb`'s `ℤ` twin: the signed limbs of element `j`. -/
def quadInt (q : Quad) (j : Fin 4) : Fin 6 → ℤ
  | 0 => vlaneInt q.v03 (j.castAdd 4)
  | 1 => vlaneInt q.v14 (j.castAdd 4)
  | 2 => vlaneInt q.v25 (j.castAdd 4)
  | 3 => vlaneInt q.v03 (j.addNat 4)
  | 4 => vlaneInt q.v14 (j.addNat 4)
  | 5 => vlaneInt q.v25 (j.addNat 4)

/-- A limb predicate on every element is one on every lane. -/
theorem lanes_of_quadInt {q : Quad} {P : ℤ → Prop} (h : ∀ j k, P (quadInt q j k)) :
    (∀ i (hi : i < 8), P (q.v03[i]'hi).toInt) ∧ (∀ i (hi : i < 8), P (q.v14[i]'hi).toInt)
      ∧ (∀ i (hi : i < 8), P (q.v25[i]'hi).toInt) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩ <;> interval_cases i
  · exact h 0 0
  · exact h 1 0
  · exact h 2 0
  · exact h 3 0
  · exact h 0 3
  · exact h 1 3
  · exact h 2 3
  · exact h 3 3
  · exact h 0 1
  · exact h 1 1
  · exact h 2 1
  · exact h 3 1
  · exact h 0 4
  · exact h 1 4
  · exact h 2 4
  · exact h 3 4
  · exact h 0 2
  · exact h 1 2
  · exact h 2 2
  · exact h 3 2
  · exact h 0 5
  · exact h 1 5
  · exact h 2 5
  · exact h 3 5

/-- **The signed fold is `foldSignedLimb` on each element**, when nothing wraps. -/
theorem quadInt_foldSignedQuad (q : Quad) (h : ∀ j k, InFold (quadInt q j k)) (j : Fin 4)
    (k : Fin 6) : quadInt (foldSignedQuad q) j k = foldSignedLimb (quadInt q j) k := by
  obtain ⟨h03, h14, h25⟩ := lanes_of_quadInt h
  fin_cases j <;> fin_cases k <;>
    simp only [quadInt, vlaneInt, foldSignedQuad, foldSignedLimb, acpLimb, biasLimb,
      Fin.reduceCastAdd, Fin.reduceAddNat, Fin.isValue, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] <;>
    first
    | rw [toInt_fsL0 (h03 _ _) (h25 _ _)]
    | rw [toInt_fsL3 (h03 _ _) (h25 _ _)]
    | rw [toInt_fsMid_b0 (h03 _ _) (h14 _ _)]
    | rw [toInt_fsMid_bb (h03 _ _) (h14 _ _)]
    | rw [toInt_fsMid_bb (h14 _ _) (h25 _ _)]
    | rw [toInt_fsMid_m40 (h14 _ _) (h25 _ _)]

/-- A limb predicate on every element is one on every lane, `ℕ` form. -/
theorem lanes_of_quadLimb {q : Quad} {P : ℕ → Prop}
    (h : ∀ j k, P (quadLimb q.v03 q.v14 q.v25 j k)) :
    (∀ i (hi : i < 8), P (q.v03[i]'hi).toNat) ∧ (∀ i (hi : i < 8), P (q.v14[i]'hi).toNat)
      ∧ (∀ i (hi : i < 8), P (q.v25[i]'hi).toNat) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩ <;> interval_cases i
  · exact h 0 0
  · exact h 1 0
  · exact h 2 0
  · exact h 3 0
  · exact h 0 3
  · exact h 1 3
  · exact h 2 3
  · exact h 3 3
  · exact h 0 1
  · exact h 1 1
  · exact h 2 1
  · exact h 3 1
  · exact h 0 4
  · exact h 1 4
  · exact h 2 4
  · exact h 3 4
  · exact h 0 2
  · exact h 1 2
  · exact h 2 2
  · exact h 3 2
  · exact h 0 5
  · exact h 1 5
  · exact h 2 5
  · exact h 3 5

private theorem unn_of_lanes {n : ℕ} {v : Vector (BitVec 64) 8}
    (h : ∀ i (hi : i < 8), 0 ≤ (v[i]'hi).toInt ∧ (v[i]'hi).toInt ≤ 2 ^ n - 1) :
    R43x6.UNN n v :=
  ⟨fun i => (h i.val i.isLt).2, fun i => (h i.val i.isLt).1⟩

/-- `UNN n` on all three vectors from a bound on every signed limb. -/
theorem unn_of_quadInt {q : Quad} {n : ℕ}
    (h : ∀ j k, 0 ≤ quadInt q j k ∧ quadInt q j k ≤ 2 ^ n - 1) :
    R43x6.UNN n q.v03 ∧ R43x6.UNN n q.v14 ∧ R43x6.UNN n q.v25 := by
  obtain ⟨h03, h14, h25⟩ := lanes_of_quadInt (P := fun x => 0 ≤ x ∧ x ≤ 2 ^ n - 1) h
  exact ⟨unn_of_lanes h03, unn_of_lanes h14, unn_of_lanes h25⟩

/-- ... and from a bound on every limb. -/
theorem unn_of_quadLimb {q : Quad} {n : ℕ} (hn : n ≤ 62)
    (h : ∀ j k, quadLimb q.v03 q.v14 q.v25 j k < 2 ^ n) :
    R43x6.UNN n q.v03 ∧ R43x6.UNN n q.v14 ∧ R43x6.UNN n q.v25 := by
  have h63 : (2 : ℕ) ^ n ≤ 2 ^ 62 := Nat.pow_le_pow_right (by omega) hn
  have key : ∀ v : BitVec 64, v.toNat < 2 ^ n → 0 ≤ v.toInt ∧ v.toInt ≤ 2 ^ n - 1 := by
    intro v hv
    rw [BitVec.toInt_eq_toNat_of_lt (by omega)]
    constructor
    · positivity
    · have : ((v.toNat : ℕ) : ℤ) < ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast hv
      push_cast at this; omega
  obtain ⟨h03, h14, h25⟩ := lanes_of_quadLimb (P := fun x => x < 2 ^ n) h
  exact ⟨unn_of_lanes fun i hi => key _ (h03 i hi), unn_of_lanes fun i hi => key _ (h14 i hi),
    unn_of_lanes fun i hi => key _ (h25 i hi)⟩

/-- The signed fold lands in `u44`. -/
theorem foldSignedLimb_bounds {x : Fin 6 → ℤ} (h : ∀ k, InFold (x k)) (k : Fin 6) :
    0 ≤ foldSignedLimb x k ∧ foldSignedLimb x k ≤ 2 ^ 44 - 1 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  simp only [InFold] at h0 h1 h2 h3 h4 h5
  fin_cases k <;> simp only [foldSignedLimb, acpLimb, biasLimb] <;> norm_num <;> omega

/-- `u44` on all three vectors. -/
abbrev QuadU44 (q : Quad) : Prop := R43x6.U44 q.v03 ∧ R43x6.U44 q.v14 ∧ R43x6.U44 q.v25

/-- `p`'s limbs, the constant `LANE_SUB_FAST` adds. -/
def pLimbI : Fin 6 → ℤ
  | 0 => 8796093022189
  | 1 => 8796093022207
  | 2 => 8796093022207
  | 3 => 8796093022207
  | 4 => 8796093022207
  | 5 => 1099511627775

theorem decodeNat_pLimbI : decodeNat pLimbI = (p : ℤ) := by
  simp [decodeNat_eq, pLimbI, p]

theorem vectorFunc_eq (q : Quad) (j : Fin 4) :
    q.vectorFunc j = quadLimb q.v03 q.v14 q.v25 j := laneFunc_vector q j

/-- An element's value, `quadElem`'s shape over any limb function. -/
abbrev elemZ (l : Fin 6 → ℕ) : ZMod p := ((decodeNat l : ℕ) : ZMod p)

theorem quadElem_eq (q : Quad) (j : Fin 4) :
    quadElem q j = elemZ (quadLimb q.v03 q.v14 q.v25 j) := by
  rw [quadElem, vectorFunc_eq]

/-- A nonnegative signed limb function decodes to its `ℕ` one. -/
theorem elemZ_of_int {l : Fin 6 → ℕ} {x : Fin 6 → ℤ} (h : ∀ k, (l k : ℤ) = x k) :
    elemZ l = ((decodeNat x : ℤ) : ZMod p) := by
  have : ((decodeNat l : ℕ) : ℤ) = decodeNat x := by
    simp only [decodeNat_eq]; push_cast; simp only [h]
  rw [elemZ, ← Int.cast_natCast, this]

private theorem toNat_eq_toInt {x : BitVec 64} (h : 0 ≤ x.toInt) : (x.toNat : ℤ) = x.toInt := by
  have hb := BitVec.toInt_eq_toNat_bmod x
  have hlt : x.toNat < 2 ^ 64 := x.isLt
  rw [Int.bmod] at hb
  split at hb <;> omega

theorem quadLimb_eq_quadInt {q : Quad} (hq : ∀ j k, 0 ≤ quadInt q j k) (j : Fin 4) (k : Fin 6) :
    (quadLimb q.v03 q.v14 q.v25 j k : ℤ) = quadInt q j k := by
  have h := hq j k
  fin_cases j <;> fin_cases k <;>
    simp only [quadInt, vlaneInt, quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat,
      Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at h ⊢ <;>
    exact toNat_eq_toInt h

end Ge

end Firedancer.Avx512

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_quad_sqr_fast
import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_quad_mul_fast
import SSA.Projects.Firedancer.Avx512.Proof.Quad
import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_point_dbln

/-!
# `FD_R43X6_GE_DBL`, as a function on QUADs

`geDbl` is the macro lane for lane as the region computes it: the lane add,
the square, the lane add/sub to `(E, G, F, H)`, the signed fold, the two
permutes, the multiply and the unsigned fold. Memory-free; the walks reduce
each instruction run to one of these definitions.

* `u44_geDbl`: `u44` in, `u44` out.
* `toPoint_geDbl`: the point is `Point.dbl` of the input's.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

namespace PointDbln

/-! ## The stages -/

/-- `%151`/`%158`/`%159` on one vector: `QUAD_PERMUTE(1,1,2,0)` and the
lane-0 add, `(X+Y, Y, Z, X)`. -/
def addXY (x : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  #v[x[1] + x[0], x[1], x[2], x[0], x[5] + x[4], x[5], x[6], x[4]]

def dblTa (q : Quad) : Quad := ⟨addXY q.v03, addXY q.v14, addXY q.v25⟩

/-- `%167`-`%199` on one vector of the square `((X+Y)², B, Z², A)`: `c`/`d`
are `p`'s limbs in the low/high half. Lanes `(E, G, F, H)`. -/
def egfh (c d : BitVec 64) (s : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  #v[s[3] + s[1] - s[0] + c, s[3] - s[1] + c, s[3] - s[1] + c + (s[2] + s[2]), s[3] + s[1],
     s[7] + s[5] - s[4] + d, s[7] - s[5] + d, s[7] - s[5] + d + (s[6] + s[6]), s[7] + s[5]]

def egfhQuad (s : Quad) : Quad :=
  ⟨egfh 8796093022189#64 8796093022207#64 s.v03, egfh 8796093022207#64 8796093022207#64 s.v14,
   egfh 8796093022207#64 1099511627775#64 s.v25⟩

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

/-- `FD_R43X6_QUAD_FOLD_SIGNED`, `%206`-`%222`. -/
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

/-- `QUAD_PERMUTE(0,1,1,0)` on one vector. -/
def permGE (v : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  #v[v[0], v[1], v[1], v[0], v[4], v[5], v[5], v[4]]

/-- `QUAD_PERMUTE(2,3,2,3)` on one vector. -/
def permFH (v : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  #v[v[2], v[3], v[2], v[3], v[6], v[7], v[6], v[7]]

def geQuad (r : Quad) : Quad := ⟨permGE r.v03, permGE r.v14, permGE r.v25⟩
def fhQuad (r : Quad) : Quad := ⟨permFH r.v03, permFH r.v14, permFH r.v25⟩

/-- `(E, G, F, H)` folded: the multiply's two operands are its permutes. -/
def dblR (q : Quad) : Quad := foldSignedQuad (egfhQuad (quadSqrResult (dblTa q)))

/-- **`FD_R43X6_GE_DBL`.** -/
def geDbl (q : Quad) : Quad := foldQuad (quadMulResult (geQuad (dblR q)) (fhQuad (dblR q)))

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

/-- `E`'s lane: `a + b - c + k`, nothing wrapping. -/
theorem toInt_laneE {a b c k : ℕ} (ha : a < 2 ^ 61) (hb : b < 2 ^ 61) (hc : c < 2 ^ 61)
    (hk : k < 2 ^ 44) :
    (BitVec.ofNat 64 a + BitVec.ofNat 64 b - BitVec.ofNat 64 c + BitVec.ofNat 64 k).toInt
      = (a : ℤ) + b - c + k := by
  rw [ofNat_eq_ofInt a, ofNat_eq_ofInt b, ofNat_eq_ofInt c, ofNat_eq_ofInt k,
    ← BitVec.ofInt_add, ofInt_sub64, ← BitVec.ofInt_add, toInt_ofInt]
  simp only [FitsLong]; omega

/-- `G`'s lane: `a - b + k`. -/
theorem toInt_laneG {a b k : ℕ} (ha : a < 2 ^ 61) (hb : b < 2 ^ 61) (hk : k < 2 ^ 44) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b + BitVec.ofNat 64 k).toInt = (a : ℤ) - b + k := by
  rw [ofNat_eq_ofInt a, ofNat_eq_ofInt b, ofNat_eq_ofInt k, ofInt_sub64, ← BitVec.ofInt_add,
    toInt_ofInt]
  simp only [FitsLong]; omega

/-- `F`'s lane: `a - b + k + (c + c)`. -/
theorem toInt_laneF {a b c k : ℕ} (ha : a < 2 ^ 61) (hb : b < 2 ^ 61) (hc : c < 2 ^ 61)
    (hk : k < 2 ^ 44) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b + BitVec.ofNat 64 k
        + (BitVec.ofNat 64 c + BitVec.ofNat 64 c)).toInt = (a : ℤ) - b + k + 2 * c := by
  rw [ofNat_eq_ofInt a, ofNat_eq_ofInt b, ofNat_eq_ofInt c, ofNat_eq_ofInt k, ofInt_sub64,
    ← BitVec.ofInt_add, ← BitVec.ofInt_add, ← BitVec.ofInt_add, toInt_ofInt]
  · ring
  · simp only [FitsLong]; omega

/-- `H`'s lane: `a + b`. -/
theorem toInt_laneH {a b : ℕ} (ha : a < 2 ^ 61) (hb : b < 2 ^ 61) :
    (BitVec.ofNat 64 a + BitVec.ofNat 64 b).toInt = (a : ℤ) + b := by
  rw [ofNat_eq_ofInt a, ofNat_eq_ofInt b, ← BitVec.ofInt_add, toInt_ofInt]
  simp only [FitsLong]; omega

/-- The signed fold's input range: what `(E, G, F, H)` occupy, with room for
the bias. -/
abbrev InFold (x : ℤ) : Prop := -2 ^ 62 ≤ x ∧ x < 2 ^ 63 - 2 ^ 29

private theorem ofInt_nb0 : (18446744073550168064#64 : BitVec 64) = BitVec.ofInt 64 (-159383552) := rfl
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

/-! ## The stages, limb by limb -/

/-- `u44` on all three vectors. -/
abbrev QuadU44 (q : Quad) : Prop := R43x6.U44 q.v03 ∧ R43x6.U44 q.v14 ∧ R43x6.U44 q.v25

private theorem toNat_add_lt {a b : BitVec 64} (ha : a.toNat < 2 ^ 44) (hb : b.toNat < 2 ^ 44) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]

theorem quadLimb_dblTa {q : Quad} (hq : QuadU44 q) :
    quadLimb (dblTa q).v03 (dblTa q).v14 (dblTa q).v25 0
        = (fun k => quadLimb q.v03 q.v14 q.v25 1 k + quadLimb q.v03 q.v14 q.v25 0 k)
      ∧ quadLimb (dblTa q).v03 (dblTa q).v14 (dblTa q).v25 1 = quadLimb q.v03 q.v14 q.v25 1
      ∧ quadLimb (dblTa q).v03 (dblTa q).v14 (dblTa q).v25 2 = quadLimb q.v03 q.v14 q.v25 2
      ∧ quadLimb (dblTa q).v03 (dblTa q).v14 (dblTa q).v25 3 = quadLimb q.v03 q.v14 q.v25 0 := by
  obtain ⟨h03, h14, h25⟩ := lanes_of_quadLimb (P := (· < 2 ^ 44))
    (quadLimb_lt q 44 (by omega) hq.1 hq.2.1 hq.2.2)
  refine ⟨funext fun k => ?_, funext fun k => ?_, funext fun k => ?_, funext fun k => ?_⟩ <;>
    fin_cases k <;> try rfl
  all_goals
    simp only [quadLimb, vlane, dblTa, addXY, Fin.reduceCastAdd, Fin.reduceAddNat, Fin.isValue,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    first
    | exact toNat_add_lt (h03 _ _) (h03 _ _)
    | exact toNat_add_lt (h14 _ _) (h14 _ _)
    | exact toNat_add_lt (h25 _ _) (h25 _ _)

theorem quadLimb_dblTa_lt {q : Quad} (hq : QuadU44 q) (j : Fin 4) (k : Fin 6) :
    quadLimb (dblTa q).v03 (dblTa q).v14 (dblTa q).v25 j k < 2 ^ 45 := by
  have hl := quadLimb_lt q 44 (by omega) hq.1 hq.2.1 hq.2.2
  obtain ⟨e0, e1, e2, e3⟩ := quadLimb_dblTa hq
  match j with
  | 0 => rw [e0]; have := hl 1 k; have := hl 0 k; simp only; omega
  | 1 => rw [e1]; exact lt_trans (hl 1 k) (by norm_num)
  | 2 => rw [e2]; exact lt_trans (hl 2 k) (by norm_num)
  | 3 => rw [e3]; exact lt_trans (hl 0 k) (by norm_num)

theorem u47_dblTa {q : Quad} (hq : QuadU44 q) :
    R43x6.U47 (dblTa q).v03 ∧ R43x6.U47 (dblTa q).v14 ∧ R43x6.U47 (dblTa q).v25 :=
  unn_of_quadLimb (by omega) fun j k => by have := quadLimb_dblTa_lt hq j k; omega

theorem quadSqrLimb_dblTa_lt {q : Quad} (hq : QuadU44 q) (j : Fin 4) (k : Fin 6) :
    quadSqrLimb (dblTa q) j k < 2 ^ 61 := by
  have hl := quadLimb_lt q 44 (by omega) hq.1 hq.2.1 hq.2.2
  obtain ⟨-, e1, e2, e3⟩ := quadLimb_dblTa hq
  simp only [quadSqrLimb]
  match j with
  | 0 => exact sqLimb_lt_u45 _ (fun i => quadLimb_dblTa_lt hq 0 i) k
  | 1 => rw [e1]; exact sqLimb_lt_u44 _ (hl 1) k
  | 2 => rw [e2]; exact sqLimb_lt_u44 _ (hl 2) k
  | 3 => rw [e3]; exact sqLimb_lt_u44 _ (hl 0) k

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

/-- **`(E, G, F, H)`, limb by limb**, from the square's limbs. -/
theorem quadInt_egfhQuad (t : Quad) (hb : ∀ j k, quadSqrLimb t j k < 2 ^ 61) (k : Fin 6) :
    quadInt (egfhQuad (quadSqrResult t)) 0 k
        = (quadSqrLimb t 3 k : ℤ) + quadSqrLimb t 1 k - quadSqrLimb t 0 k + pLimbI k
      ∧ quadInt (egfhQuad (quadSqrResult t)) 1 k
        = (quadSqrLimb t 3 k : ℤ) - quadSqrLimb t 1 k + pLimbI k
      ∧ quadInt (egfhQuad (quadSqrResult t)) 2 k
        = (quadSqrLimb t 3 k : ℤ) - quadSqrLimb t 1 k + pLimbI k + 2 * quadSqrLimb t 2 k
      ∧ quadInt (egfhQuad (quadSqrResult t)) 3 k
        = (quadSqrLimb t 3 k : ℤ) + quadSqrLimb t 1 k := by
  fin_cases k <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [quadInt, vlaneInt, egfhQuad, egfh, quadSqrResult, quadVec, pLimbI,
      Fin.reduceCastAdd, Fin.reduceAddNat, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] <;>
    first
    | rw [toInt_laneE (hb _ _) (hb _ _) (hb _ _) (by norm_num)]; norm_num
    | rw [toInt_laneF (hb _ _) (hb _ _) (hb _ _) (by norm_num)]; norm_num
    | rw [toInt_laneG (hb _ _) (hb _ _) (by norm_num)]; norm_num
    | rw [toInt_laneH (hb _ _) (hb _ _)]

theorem inFold_egfh {q : Quad} (hq : QuadU44 q) (j : Fin 4) (k : Fin 6) :
    InFold (quadInt (egfhQuad (quadSqrResult (dblTa q))) j k) := by
  have hb := quadSqrLimb_dblTa_lt hq
  obtain ⟨e0, e1, e2, e3⟩ := quadInt_egfhQuad (dblTa q) hb k
  have h0 := hb 0 k; have h1 := hb 1 k; have h2 := hb 2 k; have h3 := hb 3 k
  have hp : 0 ≤ pLimbI k ∧ pLimbI k < 2 ^ 44 := by fin_cases k <;> simp [pLimbI]
  simp only [InFold]
  match j with
  | 0 => rw [e0]; omega
  | 1 => rw [e1]; omega
  | 2 => rw [e2]; omega
  | 3 => rw [e3]; omega

theorem quadInt_dblR {q : Quad} (hq : QuadU44 q) (j : Fin 4) (k : Fin 6) :
    quadInt (dblR q) j k = foldSignedLimb (quadInt (egfhQuad (quadSqrResult (dblTa q))) j) k :=
  quadInt_foldSignedQuad _ (inFold_egfh hq) j k

theorem quadInt_dblR_bounds {q : Quad} (hq : QuadU44 q) (j : Fin 4) (k : Fin 6) :
    0 ≤ quadInt (dblR q) j k ∧ quadInt (dblR q) j k ≤ 2 ^ 44 - 1 := by
  rw [quadInt_dblR hq]; exact foldSignedLimb_bounds (inFold_egfh hq j) k

theorem u44_dblR {q : Quad} (hq : QuadU44 q) : QuadU44 (dblR q) :=
  unn_of_quadInt (quadInt_dblR_bounds hq)

private theorem unn_permGE {n : ℕ} {v : Vector (BitVec 64) 8} (h : R43x6.UNN n v) :
    R43x6.UNN n (permGE v) := by
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i
  all_goals first
    | exact h.1 0 | exact h.1 1 | exact h.1 4 | exact h.1 5
    | exact h.2 0 | exact h.2 1 | exact h.2 4 | exact h.2 5

private theorem unn_permFH {n : ℕ} {v : Vector (BitVec 64) 8} (h : R43x6.UNN n v) :
    R43x6.UNN n (permFH v) := by
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i
  all_goals first
    | exact h.1 2 | exact h.1 3 | exact h.1 6 | exact h.1 7
    | exact h.2 2 | exact h.2 3 | exact h.2 6 | exact h.2 7

theorem u44_geQuad {r : Quad} (h : QuadU44 r) : QuadU44 (geQuad r) :=
  ⟨unn_permGE h.1, unn_permGE h.2.1, unn_permGE h.2.2⟩

theorem u44_fhQuad {r : Quad} (h : QuadU44 r) : QuadU44 (fhQuad r) :=
  ⟨unn_permFH h.1, unn_permFH h.2.1, unn_permFH h.2.2⟩

theorem vectorFunc_eq (q : Quad) (j : Fin 4) :
    q.vectorFunc j = quadLimb q.v03 q.v14 q.v25 j := laneFunc_vector q j

/-- **`u44` in, `u44` out.** -/
theorem u44_geDbl {q : Quad} (hq : QuadU44 q) : QuadU44 (geDbl q) := by
  have hR := u44_dblR hq
  have hG := u44_geQuad hR
  have hF := u44_fhQuad hR
  refine unn_of_quadLimb (by omega) fun j k => ?_
  rw [← vectorFunc_eq, geDbl, laneFunc_foldQuad]
  refine foldLimb_lt (fun i => ?_) k
  rw [vectorFunc_eq, quadMul_limbs _ _ (u47_of_u44 hG.1) (u47_of_u44 hG.2.1) (u47_of_u44 hG.2.2)
    (u47_of_u44 hF.1) (u47_of_u44 hF.2.1) (u47_of_u44 hF.2.2)]
  have := quadMulLimb_lt_u44 _ _ hG.1 hG.2.1 hG.2.2 hF.1 hF.2.1 hF.2.2 j i
  omega

/-! ## The point -/

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

theorem elemZ_dblTa {q : Quad} (hq : QuadU44 q) :
    elemZ (quadLimb (dblTa q).v03 (dblTa q).v14 (dblTa q).v25 0) = quadElem q 1 + quadElem q 0
      ∧ elemZ (quadLimb (dblTa q).v03 (dblTa q).v14 (dblTa q).v25 1) = quadElem q 1
      ∧ elemZ (quadLimb (dblTa q).v03 (dblTa q).v14 (dblTa q).v25 2) = quadElem q 2
      ∧ elemZ (quadLimb (dblTa q).v03 (dblTa q).v14 (dblTa q).v25 3) = quadElem q 0 := by
  obtain ⟨e0, e1, e2, e3⟩ := quadLimb_dblTa hq
  rw [quadElem_eq, quadElem_eq, quadElem_eq, e0, e1, e2, e3]
  refine ⟨?_, rfl, rfl, rfl⟩
  simp only [elemZ, decodeNat_eq]; push_cast; ring

theorem elemZ_sqr (t : Quad) (j : Fin 4) :
    elemZ (quadSqrLimb t j) = elemZ (quadLimb t.v03 t.v14 t.v25 j) ^ 2 :=
  decodeLimbs_sqLimb_zmod _

/-- The signed limbs of `(E, G, F, H)`, in the field. -/
theorem zmod_egfh {q : Quad} (hq : QuadU44 q) :
    ((decodeNat (quadInt (egfhQuad (quadSqrResult (dblTa q))) 0) : ℤ) : ZMod p)
        = elemZ (quadSqrLimb (dblTa q) 3) + elemZ (quadSqrLimb (dblTa q) 1)
          - elemZ (quadSqrLimb (dblTa q) 0)
      ∧ ((decodeNat (quadInt (egfhQuad (quadSqrResult (dblTa q))) 1) : ℤ) : ZMod p)
        = elemZ (quadSqrLimb (dblTa q) 3) - elemZ (quadSqrLimb (dblTa q) 1)
      ∧ ((decodeNat (quadInt (egfhQuad (quadSqrResult (dblTa q))) 2) : ℤ) : ZMod p)
        = elemZ (quadSqrLimb (dblTa q) 3) - elemZ (quadSqrLimb (dblTa q) 1)
          + 2 * elemZ (quadSqrLimb (dblTa q) 2)
      ∧ ((decodeNat (quadInt (egfhQuad (quadSqrResult (dblTa q))) 3) : ℤ) : ZMod p)
        = elemZ (quadSqrLimb (dblTa q) 3) + elemZ (quadSqrLimb (dblTa q) 1) := by
  have hb := quadSqrLimb_dblTa_lt hq
  have hP : ((decodeNat pLimbI : ℤ) : ZMod p) = 0 := by
    rw [decodeNat_pLimbI]; simp
  have c : ∀ j, elemZ (quadSqrLimb (dblTa q) j)
      = ((decodeNat (fun k => (quadSqrLimb (dblTa q) j k : ℤ)) : ℤ) : ZMod p) :=
    fun j => elemZ_of_int fun _ => rfl
  simp only [c]
  have e : ∀ j, quadInt (egfhQuad (quadSqrResult (dblTa q))) j
      = fun k => quadInt (egfhQuad (quadSqrResult (dblTa q))) j k := fun _ => rfl
  rw [e 0, e 1, e 2, e 3]
  simp only [fun k => (quadInt_egfhQuad (dblTa q) hb k).1,
    fun k => (quadInt_egfhQuad (dblTa q) hb k).2.1,
    fun k => (quadInt_egfhQuad (dblTa q) hb k).2.2.1,
    fun k => (quadInt_egfhQuad (dblTa q) hb k).2.2.2]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [← sub_eq_zero, ← hP]; simp only [decodeNat_eq]; push_cast; ring_nf; done)
    | (simp only [decodeNat_eq]; push_cast; ring_nf)

theorem elemZ_dblR {q : Quad} (hq : QuadU44 q) (j : Fin 4) :
    elemZ (quadLimb (dblR q).v03 (dblR q).v14 (dblR q).v25 j)
      = ((decodeNat (quadInt (egfhQuad (quadSqrResult (dblTa q))) j) : ℤ) : ZMod p) := by
  rw [elemZ_of_int (quadLimb_eq_quadInt (fun j k => (quadInt_dblR_bounds hq j k).1) j),
    show quadInt (dblR q) j = foldSignedLimb (quadInt (egfhQuad (quadSqrResult (dblTa q))) j)
      from funext (quadInt_dblR hq j), decodeNat_foldSignedLimb_zmod]

theorem quadLimb_geQuad (r : Quad) :
    quadLimb (geQuad r).v03 (geQuad r).v14 (geQuad r).v25 0 = quadLimb r.v03 r.v14 r.v25 0
      ∧ quadLimb (geQuad r).v03 (geQuad r).v14 (geQuad r).v25 1 = quadLimb r.v03 r.v14 r.v25 1
      ∧ quadLimb (geQuad r).v03 (geQuad r).v14 (geQuad r).v25 2 = quadLimb r.v03 r.v14 r.v25 1
      ∧ quadLimb (geQuad r).v03 (geQuad r).v14 (geQuad r).v25 3 = quadLimb r.v03 r.v14 r.v25 0 := by
  refine ⟨funext fun k => ?_, funext fun k => ?_, funext fun k => ?_, funext fun k => ?_⟩ <;>
    fin_cases k <;> rfl

theorem quadLimb_fhQuad (r : Quad) :
    quadLimb (fhQuad r).v03 (fhQuad r).v14 (fhQuad r).v25 0 = quadLimb r.v03 r.v14 r.v25 2
      ∧ quadLimb (fhQuad r).v03 (fhQuad r).v14 (fhQuad r).v25 1 = quadLimb r.v03 r.v14 r.v25 3
      ∧ quadLimb (fhQuad r).v03 (fhQuad r).v14 (fhQuad r).v25 2 = quadLimb r.v03 r.v14 r.v25 2
      ∧ quadLimb (fhQuad r).v03 (fhQuad r).v14 (fhQuad r).v25 3 = quadLimb r.v03 r.v14 r.v25 3 := by
  refine ⟨funext fun k => ?_, funext fun k => ?_, funext fun k => ?_, funext fun k => ?_⟩ <;>
    fin_cases k <;> rfl

/-- Element `j` of the result: the product of the multiply's operands. -/
theorem quadElem_geDbl {q : Quad} (hq : QuadU44 q) (j : Fin 4) :
    quadElem (geDbl q) j
      = elemZ (quadLimb (geQuad (dblR q)).v03 (geQuad (dblR q)).v14 (geQuad (dblR q)).v25 j)
        * elemZ (quadLimb (fhQuad (dblR q)).v03 (fhQuad (dblR q)).v14 (fhQuad (dblR q)).v25 j) := by
  have hR := u44_dblR hq
  have hG := u44_geQuad hR
  have hF := u44_fhQuad hR
  rw [geDbl, quadElem_foldQuad, quadElem_eq,
    show quadLimb _ _ _ j = quadMulLimb (geQuad (dblR q)) (fhQuad (dblR q)) j from
      funext (quadMul_limbs _ _ (u47_of_u44 hG.1) (u47_of_u44 hG.2.1) (u47_of_u44 hG.2.2)
        (u47_of_u44 hF.1) (u47_of_u44 hF.2.1) (u47_of_u44 hF.2.2) j),
    elemZ, quadMul_zmod, laneFunc_vector, laneFunc_vector]

/-- **`FD_R43X6_GE_DBL` doubles**: the point is `Point.dbl` of the input's. -/
theorem toPoint_geDbl {q : Quad} (hq : QuadU44 q) : (geDbl q).toPoint = q.toPoint.dbl := by
  obtain ⟨g0, g1, g2, g3⟩ := quadLimb_geQuad (dblR q)
  obtain ⟨f0, f1, f2, f3⟩ := quadLimb_fhQuad (dblR q)
  obtain ⟨p0, p1, p2, p3⟩ := zmod_egfh hq
  obtain ⟨t0, t1, t2, t3⟩ := elemZ_dblTa hq
  have e0 := quadElem_geDbl hq 0
  have e1 := quadElem_geDbl hq 1
  have e2 := quadElem_geDbl hq 2
  have e3 := quadElem_geDbl hq 3
  rw [g0, f0, elemZ_dblR hq, elemZ_dblR hq, p0, p2] at e0
  rw [g1, f1, elemZ_dblR hq, elemZ_dblR hq, p1, p3] at e1
  rw [g2, f2, elemZ_dblR hq, elemZ_dblR hq, p1, p2] at e2
  rw [g3, f3, elemZ_dblR hq, elemZ_dblR hq, p0, p3] at e3
  simp only [elemZ_sqr, t0, t1, t2, t3] at e0 e1 e2 e3
  show Point.mk (quadElem (geDbl q) 0) (quadElem (geDbl q) 1) (quadElem (geDbl q) 2)
      (quadElem (geDbl q) 3)
    = Point.dbl ⟨quadElem q 0, quadElem q 1, quadElem q 2, quadElem q 3⟩
  rw [e0, e1, e2, e3]
  simp only [Point.dbl, Point.mk.injEq]
  exact ⟨by ring, trivial, by ring, by ring⟩

end PointDbln

end Firedancer.Avx512

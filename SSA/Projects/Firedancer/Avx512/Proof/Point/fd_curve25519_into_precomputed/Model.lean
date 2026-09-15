/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Proof.Point.Ge.Lanes
import SSA.Projects.Firedancer.Common.Spec.fd_curve25519_into_precomputed

/-!
# `fd_curve25519_into_precomputed`, as a function on QUADs

`intoPre q`: the lane sub/add to `(Y-X, Y+X, Z, T)`, the signed fold, the multiply
by `(1, 1, 1, 2d)`, the unsigned fold.

* `u44_intoPre`: `u62` in, `u44` out.
* `ofSlots_intoPre`: the slots hold `Point.toPrecomputed`.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

namespace IntoPre
open Ge

/-! ## The stages -/

/-- `%65`-`%82` on one vector: `(Y-X+c, X+Y, Z, T)`, `c`/`d` `p`'s limbs in the low/high
half. -/
def ipVec (c d : BitVec 64) (x : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  #v[x[1] - x[0] + c, x[0] + x[1], x[2], x[3], x[5] - x[4] + d, x[4] + x[5], x[6], x[7]]

def ipQuad (q : Quad) : Quad :=
  ⟨ipVec 8796093022189#64 8796093022207#64 q.v03, ipVec 8796093022207#64 8796093022207#64 q.v14,
   ipVec 8796093022207#64 1099511627775#64 q.v25⟩

/-- The folded lanes, the multiply's first operand. -/
def ipF (q : Quad) : Quad := foldSignedQuad (ipQuad q)

/-- `FD_R43X6_QUAD_1112d`, `%2`/`%1`/`%0`. -/
def c1112d : Quad :=
  ⟨#v[1#64, 1#64, 1#64, 3934839304537#64, 0#64, 0#64, 0#64, 521695520920#64],
   #v[0#64, 0#64, 0#64, 507525298899#64, 0#64, 0#64, 0#64, 6596238350568#64],
   #v[0#64, 0#64, 0#64, 15037786634#64, 0#64, 0#64, 0#64, 309467527341#64]⟩

/-- **`fd_curve25519_into_precomputed`.** -/
def intoPre (q : Quad) : Quad := foldQuad (quadMulResult (ipF q) c1112d)

/-- `u62` on all three vectors. -/
abbrev QuadU62 (q : Quad) : Prop := R43x6.U62 q.v03 ∧ R43x6.U62 q.v14 ∧ R43x6.U62 q.v25

/-! ## The signed fold on wider input

`Ge`'s lemmas, copied over `InFoldW`: `Ge.InFold` asks `x < 2^63 - 2^29`, which `Y + X`
of two `u62` limbs can exceed, and no proof uses that margin. -/

section Fold
open R43x6 (FitsLong)

/-- `Ge.InFold` without its unused upper margin. -/
abbrev InFoldW (x : ℤ) : Prop := -2 ^ 62 ≤ x ∧ x < 2 ^ 63

private theorem toInt_add_ofInt {x : BitVec 64} {c : ℤ} (h : FitsLong (x.toInt + c)) :
    (x + BitVec.ofInt 64 c).toInt = x.toInt + c := by
  rw [← toInt_ofInt h, BitVec.ofInt_add, ofInt_toInt]

private theorem ofInt_nb0 :
    (18446744073550168064#64 : BitVec 64) = BitVec.ofInt 64 (-159383552) := rfl
private theorem ofInt_nb : (18446744073708503040#64 : BitVec 64) = BitVec.ofInt 64 (-1048576) := rfl

theorem toInt_fsL0 {x y : BitVec 64} (hx : InFoldW x.toInt) (hy : InFoldW y.toInt) :
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

theorem toInt_fsL3 {x y : BitVec 64} (hx : InFoldW x.toInt) (hy : InFoldW y.toInt) :
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

theorem toInt_fsMid_b0 {x y : BitVec 64} (hx : InFoldW x.toInt) (hy : InFoldW y.toInt) :
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

theorem toInt_fsMid_bb {x y : BitVec 64} (hx : InFoldW x.toInt) (hy : InFoldW y.toInt) :
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

theorem toInt_fsMid_m40 {x y : BitVec 64} (hx : InFoldW x.toInt) (hy : InFoldW y.toInt) :
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

/-- `Ge.quadInt_foldSignedQuad` under `InFoldW`. -/
theorem quadInt_foldSignedQuad (q : Quad) (h : ∀ j k, InFoldW (quadInt q j k)) (j : Fin 4)
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

/-- `Ge.foldSignedLimb_bounds` under `InFoldW`. -/
theorem foldSignedLimb_bounds {x : Fin 6 → ℤ} (h : ∀ k, InFoldW (x k)) (k : Fin 6) :
    0 ≤ foldSignedLimb x k ∧ foldSignedLimb x k ≤ 2 ^ 44 - 1 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  simp only [InFoldW] at h0 h1 h2 h3 h4 h5
  fin_cases k <;> simp only [foldSignedLimb, acpLimb, biasLimb] <;> norm_num <;> omega

end Fold

/-! ## The lane sub/add over `ℤ` -/

theorem toInt_of_lt62 {x : BitVec 64} (h : x.toNat < 2 ^ 62) : x.toInt = x.toNat :=
  BitVec.toInt_eq_toNat_of_lt (by omega)

theorem toInt_add62 {x y : BitVec 64} (hx : x.toNat < 2 ^ 62) (hy : y.toNat < 2 ^ 62) :
    (x + y).toInt = (x.toNat : ℤ) + y.toNat := by
  rw [BitVec.toInt_eq_toNat_of_lt (by rw [BitVec.toNat_add]; omega), BitVec.toNat_add,
    Nat.mod_eq_of_lt (by omega)]
  push_cast; rfl

theorem toInt_sub_add62 {x y c : BitVec 64} (hx : x.toNat < 2 ^ 62) (hy : y.toNat < 2 ^ 62)
    (hc : c.toNat < 2 ^ 44) : (x - y + c).toInt = (x.toNat : ℤ) - y.toNat + c.toNat := by
  rw [BitVec.toInt_add, BitVec.toInt_sub, toInt_of_lt62 hx, toInt_of_lt62 hy,
    toInt_of_lt62 (by omega : c.toNat < 2 ^ 62)]
  simp only [Int.bmod]
  split <;> split <;> omega

/-- Every lane of a `u62` QUAD, below `2^62`. -/
theorem lanes62 {q : Quad} (hq : QuadU62 q) :
    (∀ i (hi : i < 8), (q.v03[i]'hi).toNat < 2 ^ 62)
      ∧ (∀ i (hi : i < 8), (q.v14[i]'hi).toNat < 2 ^ 62)
      ∧ (∀ i (hi : i < 8), (q.v25[i]'hi).toNat < 2 ^ 62) :=
  lanes_of_quadLimb (P := (· < 2 ^ 62)) (quadLimb_lt q 62 le_rfl hq.1 hq.2.1 hq.2.2)

theorem toInt_sub_add_ofNat62 {x y : BitVec 64} {c : ℕ} (hx : x.toNat < 2 ^ 62)
    (hy : y.toNat < 2 ^ 62) (hc : c < 2 ^ 44) :
    (x - y + BitVec.ofNat 64 c).toInt = (x.toNat : ℤ) - y.toNat + c := by
  have hc' : (BitVec.ofNat 64 c).toNat = c := by simp; omega
  rw [toInt_sub_add62 hx hy (c := BitVec.ofNat 64 c) (by rw [hc']; omega), hc']

theorem quadInt_ipQuad {q : Quad} (hq : QuadU62 q) (k : Fin 6) :
    quadInt (ipQuad q) 0 k
        = (quadLimb q.v03 q.v14 q.v25 1 k : ℤ) - quadLimb q.v03 q.v14 q.v25 0 k + pLimbI k
      ∧ quadInt (ipQuad q) 1 k
        = (quadLimb q.v03 q.v14 q.v25 0 k : ℤ) + quadLimb q.v03 q.v14 q.v25 1 k
      ∧ quadInt (ipQuad q) 2 k = quadLimb q.v03 q.v14 q.v25 2 k
      ∧ quadInt (ipQuad q) 3 k = quadLimb q.v03 q.v14 q.v25 3 k := by
  obtain ⟨b03, b14, b25⟩ := lanes62 hq
  fin_cases k <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [quadInt, vlaneInt, ipQuad, ipVec, quadLimb, vlane, pLimbI,
      Fin.reduceCastAdd, Fin.reduceAddNat, Fin.isValue,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] <;>
    first
    | (rw [toInt_sub_add_ofNat62 (b03 _ _) (b03 _ _)] <;> norm_num)
    | (rw [toInt_sub_add_ofNat62 (b14 _ _) (b14 _ _)] <;> norm_num)
    | (rw [toInt_sub_add_ofNat62 (b25 _ _) (b25 _ _)] <;> norm_num)
    | rw [toInt_add62 (b03 _ _) (b03 _ _)]
    | rw [toInt_add62 (b14 _ _) (b14 _ _)]
    | rw [toInt_add62 (b25 _ _) (b25 _ _)]
    | rw [toInt_of_lt62 (b03 _ _)]
    | rw [toInt_of_lt62 (b14 _ _)]
    | rw [toInt_of_lt62 (b25 _ _)]

theorem inFold_ip {q : Quad} (hq : QuadU62 q) (j : Fin 4) (k : Fin 6) :
    InFoldW (quadInt (ipQuad q) j k) := by
  have hl := quadLimb_lt q 62 le_rfl hq.1 hq.2.1 hq.2.2
  obtain ⟨e0, e1, e2, e3⟩ := quadInt_ipQuad hq k
  have h0 := hl 0 k; have h1 := hl 1 k; have h2 := hl 2 k; have h3 := hl 3 k
  have hp : 0 ≤ pLimbI k ∧ pLimbI k < 2 ^ 44 := by fin_cases k <;> simp [pLimbI]
  simp only [InFoldW]
  match j with
  | 0 => rw [e0]; omega
  | 1 => rw [e1]; omega
  | 2 => rw [e2]; omega
  | 3 => rw [e3]; omega

theorem quadInt_ipF_bounds {q : Quad} (hq : QuadU62 q) (j : Fin 4) (k : Fin 6) :
    0 ≤ quadInt (ipF q) j k ∧ quadInt (ipF q) j k ≤ 2 ^ 44 - 1 := by
  rw [ipF, quadInt_foldSignedQuad _ (inFold_ip hq)]
  exact foldSignedLimb_bounds (inFold_ip hq j) k

theorem u44_ipF {q : Quad} (hq : QuadU62 q) : QuadU44 (ipF q) :=
  unn_of_quadInt (quadInt_ipF_bounds hq)

theorem elemZ_ipF {q : Quad} (hq : QuadU62 q) (j : Fin 4) :
    elemZ (quadLimb (ipF q).v03 (ipF q).v14 (ipF q).v25 j)
      = ((decodeNat (quadInt (ipQuad q) j) : ℤ) : ZMod p) := by
  rw [elemZ_of_int (quadLimb_eq_quadInt (fun j k => (quadInt_ipF_bounds hq j k).1) j),
    show quadInt (ipF q) j = foldSignedLimb (quadInt (ipQuad q) j)
      from funext (quadInt_foldSignedQuad _ (inFold_ip hq) j), decodeNat_foldSignedLimb_zmod]

/-- `PointAdd.quadElem_int`. -/
theorem quadElem_int (q : Quad) (j : Fin 4) :
    quadElem q j = ((decodeNat (fun k => (quadLimb q.v03 q.v14 q.v25 j k : ℤ)) : ℤ) : ZMod p) :=
  (quadElem_eq q j).trans (elemZ_of_int fun _ => rfl)

/-- `PointAdd.pLimbI_zmod`. -/
theorem pLimbI_zmod : ((decodeNat pLimbI : ℤ) : ZMod p) = 0 := by
  rw [decodeNat_pLimbI]; simp

/-- The lanes in the field: `(Y - X, X + Y, Z, T)`. -/
theorem zmod_ip {q : Quad} (hq : QuadU62 q) :
    ((decodeNat (quadInt (ipQuad q) 0) : ℤ) : ZMod p) = quadElem q 1 - quadElem q 0
      ∧ ((decodeNat (quadInt (ipQuad q) 1) : ℤ) : ZMod p) = quadElem q 0 + quadElem q 1
      ∧ ((decodeNat (quadInt (ipQuad q) 2) : ℤ) : ZMod p) = quadElem q 2
      ∧ ((decodeNat (quadInt (ipQuad q) 3) : ℤ) : ZMod p) = quadElem q 3 := by
  have hP := pLimbI_zmod
  simp only [quadElem_int]
  have e : ∀ j, quadInt (ipQuad q) j = fun k => quadInt (ipQuad q) j k := fun _ => rfl
  rw [e 0, e 1, e 2, e 3]
  simp only [fun k => (quadInt_ipQuad hq k).1, fun k => (quadInt_ipQuad hq k).2.1,
    fun k => (quadInt_ipQuad hq k).2.2.1, fun k => (quadInt_ipQuad hq k).2.2.2]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [← sub_eq_zero, ← hP]; simp only [decodeNat_eq]; push_cast; ring_nf; done)
    | (simp only [decodeNat_eq] <;> push_cast <;> ring_nf)

/-! ## The multiply by `(1, 1, 1, 2d)` -/

theorem u44_c1112d : QuadU44 c1112d := by
  refine ⟨⟨fun i => ?_, fun i => ?_⟩, ⟨fun i => ?_, fun i => ?_⟩, ⟨fun i => ?_, fun i => ?_⟩⟩ <;>
    fin_cases i <;> decide

theorem quadElem_c1112d :
    quadElem c1112d 0 = 1 ∧ quadElem c1112d 1 = 1 ∧ quadElem c1112d 2 = 1
      ∧ quadElem c1112d 3 = 2 * d := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- `u44` is `u62`. -/
theorem u62_of_u44 {v : Vector (BitVec 64) 8} (h : R43x6.U44 v) : R43x6.U62 v :=
  ⟨fun i => (h.1 i).trans (by norm_num), h.2⟩

theorem u47s {q : Quad} (h : QuadU44 q) :
    R43x6.U47 q.v03 ∧ R43x6.U47 q.v14 ∧ R43x6.U47 q.v25 :=
  ⟨u47_of_u44 h.1, u47_of_u44 h.2.1, u47_of_u44 h.2.2⟩

/-- **`u62` in, `u44` out.** -/
theorem u44_intoPre {q : Quad} (hq : QuadU62 q) : QuadU44 (intoPre q) := by
  have hF := u44_ipF hq
  have hC := u44_c1112d
  refine unn_of_quadLimb (by omega) fun j k => ?_
  rw [← vectorFunc_eq, intoPre, laneFunc_foldQuad]
  refine foldLimb_lt (fun i => ?_) k
  rw [vectorFunc_eq, quadMul_limbs _ _ (u47_of_u44 hF.1) (u47_of_u44 hF.2.1) (u47_of_u44 hF.2.2)
    (u47_of_u44 hC.1) (u47_of_u44 hC.2.1) (u47_of_u44 hC.2.2)]
  have := quadMulLimb_lt_u44 _ _ hF.1 hF.2.1 hF.2.2 hC.1 hC.2.1 hC.2.2 j i
  omega

theorem quadElem_intoPre {q : Quad} (hq : QuadU62 q) (j : Fin 4) :
    quadElem (intoPre q) j
      = ((decodeNat (quadInt (ipQuad q) j) : ℤ) : ZMod p) * quadElem c1112d j := by
  have hF := u44_ipF hq
  have hC := u44_c1112d
  rw [intoPre, quadElem_foldQuad, quadElem_eq,
    show quadLimb _ _ _ j = quadMulLimb (ipF q) c1112d j from
      funext (quadMul_limbs _ _ (u47_of_u44 hF.1) (u47_of_u44 hF.2.1) (u47_of_u44 hF.2.2)
        (u47_of_u44 hC.1) (u47_of_u44 hC.2.1) (u47_of_u44 hC.2.2) j),
    elemZ, quadMul_zmod, laneFunc_vector, laneFunc_vector, ← elemZ_ipF hq, quadElem_eq]

/-- **The slots hold the precomputed point.** -/
theorem ofSlots_intoPre {q : Quad} (hq : QuadU62 q) :
    PrecomputedPoint.ofSlots (intoPre q).toPoint = q.toPoint.toPrecomputed := by
  obtain ⟨t0, t1, t2, t3⟩ := zmod_ip hq
  obtain ⟨c0, c1, c2, c3⟩ := quadElem_c1112d
  show PrecomputedPoint.mk (quadElem (intoPre q) 0) (quadElem (intoPre q) 1)
      (quadElem (intoPre q) 2) (quadElem (intoPre q) 3)
    = Point.toPrecomputed ⟨quadElem q 0, quadElem q 1, quadElem q 2, quadElem q 3⟩
  rw [quadElem_intoPre hq, quadElem_intoPre hq, quadElem_intoPre hq, quadElem_intoPre hq,
    t0, t1, t2, t3, c0, c1, c2, c3]
  simp only [Point.toPrecomputed, PrecomputedPoint.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-! ## The run -/

/-- **`%65`/`%72`/`%73`/`%74`/`%81`/`%82`**: `(Y-X+c, X+Y, Z, T)`. -/
theorem denote_ip {x : Vector (BitVec 64) 8} {c d : BitVec 64}
    {z m a b e f g h : Vector (LLVM.IntW 64) 8} (hm : m = pmaskE c d)
    (ha : a = vshuf [1, 0, 2, 3, 5, 4, 6, 7] (x.map PoisonOr.value) z)
    (hb : b = vbin .sub a (x.map PoisonOr.value))
    (he : e = vbin .add b m)
    (hf : f = vshuf [0, 9, 10, 11, 4, 13, 14, 15] e a)
    (hg : g = vbin .add f (x.map PoisonOr.value))
    (hh : h = vshuf [0, 9, 2, 3, 4, 13, 6, 7] f g) :
    h = (ipVec c d x).map PoisonOr.value := by
  subst hm
  replace ha : a = (#v[x[1], x[0], x[2], x[3], x[5], x[4], x[6], x[7]]
      : Vector (BitVec 64) 8).map PoisonOr.value := by subst ha; ge_lanes []
  subst ha
  replace hb : b = (#v[x[1] - x[0], x[0] - x[1], x[2] - x[2], x[3] - x[3], x[5] - x[4],
      x[4] - x[5], x[6] - x[6], x[7] - x[7]] : Vector (BitVec 64) 8).map PoisonOr.value := by
    subst hb; ge_lanes [sub_value]
  subst hb
  replace hf : f = (#v[x[1] - x[0] + c, x[0], x[2], x[3], x[5] - x[4] + d, x[4], x[6], x[7]]
      : Vector (BitVec 64) 8).map PoisonOr.value := by
    subst he hf; ge_lanes [pmaskE, add_value]
  subst hf hg hh
  ge_lanes [ipVec, add_value]

end IntoPre

end Firedancer.Avx512

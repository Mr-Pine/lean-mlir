/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Proof.Point.Ge.Model
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
open Ge

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

/-! ## `E` and `F` over `ℤ` -/

section Lanes
open R43x6 (FitsLong)

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

/-- `F`'s lane: `a - b + k + (c + c)`. -/
theorem toInt_laneF {a b c k : ℕ} (ha : a < 2 ^ 61) (hb : b < 2 ^ 61) (hc : c < 2 ^ 61)
    (hk : k < 2 ^ 44) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b + BitVec.ofNat 64 k
        + (BitVec.ofNat 64 c + BitVec.ofNat 64 c)).toInt = (a : ℤ) - b + k + 2 * c := by
  rw [ofNat_eq_ofInt a, ofNat_eq_ofInt b, ofNat_eq_ofInt c, ofNat_eq_ofInt k, ofInt_sub64,
    ← BitVec.ofInt_add, ← BitVec.ofInt_add, ← BitVec.ofInt_add, toInt_ofInt]
  · ring
  · simp only [FitsLong]; omega

end Lanes

/-! ## The stages, limb by limb -/

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

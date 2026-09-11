/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Proof.Point.Ge.Model
import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_point_add_with_opts

/-!
# `FD_R43X6_GE_ADD_TABLE_ALT`, as a function on QUADs

`geAddTable a b` is the macro lane for lane: `a`'s lane sub/add to
`(Y-X, Y+X, 2Z, T)`, the signed fold, the multiply by the table point `b`, the
unsigned fold, the lane sub/add to `(E, H, G, F)`, the signed fold, the two
permutes, the multiply and the unsigned fold.

* `u44_geAddTable`: `u44` in, `u44` out.
* `toPoint_geAddTable`: the point is `Point.addPrecomputed`.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

namespace PointAdd
open Ge

/-! ## The stages -/

/-- `%161`-`%179` on one vector of `a`: `(Y-X+c, X+Y, Z+Z, T)`, `c`/`d` `p`'s limbs in the
low/high half. -/
def tbVec (c d : BitVec 64) (x : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  #v[x[1] - x[0] + c, x[0] + x[1], x[2] + x[2], x[3],
     x[5] - x[4] + d, x[4] + x[5], x[6] + x[6], x[7]]

def tbQuad (q : Quad) : Quad :=
  ⟨tbVec 8796093022189#64 8796093022207#64 q.v03, tbVec 8796093022207#64 8796093022207#64 q.v14,
   tbVec 8796093022207#64 1099511627775#64 q.v25⟩

/-- `%215`-`%228` on one vector of `(A, B, D, C)`: `(B-A+c, A+B, C+D, D-C+c)`. -/
def ehgfVec (c d : BitVec 64) (v : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  #v[v[1] - v[0] + c, v[0] + v[1], v[3] + v[2], v[2] - v[3] + c,
     v[5] - v[4] + d, v[4] + v[5], v[7] + v[6], v[6] - v[7] + d]

def ehgfQuad (q : Quad) : Quad :=
  ⟨ehgfVec 8796093022189#64 8796093022207#64 q.v03,
   ehgfVec 8796093022207#64 8796093022207#64 q.v14,
   ehgfVec 8796093022207#64 1099511627775#64 q.v25⟩

/-- `QUAD_PERMUTE(0,2,2,0)` on one vector. -/
def permEGGE (v : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  #v[v[0], v[2], v[2], v[0], v[4], v[6], v[6], v[4]]

/-- `QUAD_PERMUTE(3,1,3,1)` on one vector. -/
def permFHFH (v : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  #v[v[3], v[1], v[3], v[1], v[7], v[5], v[7], v[5]]

def egegQuad (r : Quad) : Quad := ⟨permEGGE r.v03, permEGGE r.v14, permEGGE r.v25⟩
def fhfhQuad (r : Quad) : Quad := ⟨permFHFH r.v03, permFHFH r.v14, permFHFH r.v25⟩

/-- `a`'s lanes folded, the multiply's second operand. -/
def tbF (q : Quad) : Quad := foldSignedQuad (tbQuad q)

/-- `(A, B, D, C)`: the table point times `tbF a`, folded. -/
def addA (a b : Quad) : Quad := foldQuad (quadMulResult b (tbF a))

/-- `(E, H, G, F)` folded. -/
def addR (a b : Quad) : Quad := foldSignedQuad (ehgfQuad (addA a b))

/-- **`FD_R43X6_GE_ADD_TABLE_ALT`.** -/
def geAddTable (a b : Quad) : Quad :=
  foldQuad (quadMulResult (egegQuad (addR a b)) (fhfhQuad (addR a b)))

/-! ## Lanes over `ℤ` -/

theorem toInt_of_lt {x : BitVec 64} (h : x.toNat < 2 ^ 61) : x.toInt = x.toNat :=
  BitVec.toInt_eq_toNat_of_lt (by omega)

theorem toInt_add_lt {x y : BitVec 64} (hx : x.toNat < 2 ^ 61) (hy : y.toNat < 2 ^ 61) :
    (x + y).toInt = (x.toNat : ℤ) + y.toNat := by
  have := toInt_laneH hx hy
  simpa using this

theorem toInt_sub_add_lt {x y c : BitVec 64} (hx : x.toNat < 2 ^ 61) (hy : y.toNat < 2 ^ 61)
    (hc : c.toNat < 2 ^ 44) : (x - y + c).toInt = (x.toNat : ℤ) - y.toNat + c.toNat := by
  have := toInt_laneG hx hy hc
  simpa using this

/-- Every lane of a `u44` QUAD, below `2^44`. -/
theorem lanes_u44 {q : Quad} (hq : QuadU44 q) :
    (∀ i (hi : i < 8), (q.v03[i]'hi).toNat < 2 ^ 44)
      ∧ (∀ i (hi : i < 8), (q.v14[i]'hi).toNat < 2 ^ 44)
      ∧ (∀ i (hi : i < 8), (q.v25[i]'hi).toNat < 2 ^ 44) :=
  lanes_of_quadLimb (P := (· < 2 ^ 44)) (quadLimb_lt q 44 (by omega) hq.1 hq.2.1 hq.2.2)

/-- ... below `2^61`, the form the `toInt` lane lemmas take. -/
theorem lanes61 {q : Quad} (hq : QuadU44 q) :
    (∀ i (hi : i < 8), (q.v03[i]'hi).toNat < 2 ^ 61)
      ∧ (∀ i (hi : i < 8), (q.v14[i]'hi).toNat < 2 ^ 61)
      ∧ (∀ i (hi : i < 8), (q.v25[i]'hi).toNat < 2 ^ 61) := by
  obtain ⟨h03, h14, h25⟩ := lanes_u44 hq
  exact ⟨fun i hi => lt_trans (h03 i hi) (by norm_num),
    fun i hi => lt_trans (h14 i hi) (by norm_num), fun i hi => lt_trans (h25 i hi) (by norm_num)⟩

theorem toInt_sub_add_ofNat {x y : BitVec 64} {c : ℕ} (hx : x.toNat < 2 ^ 61)
    (hy : y.toNat < 2 ^ 61) (hc : c < 2 ^ 44) :
    (x - y + BitVec.ofNat 64 c).toInt = (x.toNat : ℤ) - y.toNat + c := by
  have hc' : (BitVec.ofNat 64 c).toNat = c := by simp; omega
  rw [toInt_sub_add_lt hx hy (c := BitVec.ofNat 64 c) (by rw [hc']; omega), hc']

/-! ## `a`'s lanes -/

theorem quadInt_tbQuad {q : Quad} (hq : QuadU44 q) (k : Fin 6) :
    quadInt (tbQuad q) 0 k
        = (quadLimb q.v03 q.v14 q.v25 1 k : ℤ) - quadLimb q.v03 q.v14 q.v25 0 k + pLimbI k
      ∧ quadInt (tbQuad q) 1 k
        = (quadLimb q.v03 q.v14 q.v25 0 k : ℤ) + quadLimb q.v03 q.v14 q.v25 1 k
      ∧ quadInt (tbQuad q) 2 k
        = (quadLimb q.v03 q.v14 q.v25 2 k : ℤ) + quadLimb q.v03 q.v14 q.v25 2 k
      ∧ quadInt (tbQuad q) 3 k = quadLimb q.v03 q.v14 q.v25 3 k := by
  obtain ⟨b03, b14, b25⟩ := lanes61 hq
  fin_cases k <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [quadInt, vlaneInt, tbQuad, tbVec, quadLimb, vlane, pLimbI,
      Fin.reduceCastAdd, Fin.reduceAddNat, Fin.isValue,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] <;>
    first
    | (rw [toInt_sub_add_ofNat (b03 _ _) (b03 _ _)] <;> norm_num)
    | (rw [toInt_sub_add_ofNat (b14 _ _) (b14 _ _)] <;> norm_num)
    | (rw [toInt_sub_add_ofNat (b25 _ _) (b25 _ _)] <;> norm_num)
    | rw [toInt_add_lt (b03 _ _) (b03 _ _)]
    | rw [toInt_add_lt (b14 _ _) (b14 _ _)]
    | rw [toInt_add_lt (b25 _ _) (b25 _ _)]
    | rw [toInt_of_lt (b03 _ _)]
    | rw [toInt_of_lt (b14 _ _)]
    | rw [toInt_of_lt (b25 _ _)]

theorem inFold_tb {q : Quad} (hq : QuadU44 q) (j : Fin 4) (k : Fin 6) :
    InFold (quadInt (tbQuad q) j k) := by
  have hl := quadLimb_lt q 44 (by omega) hq.1 hq.2.1 hq.2.2
  obtain ⟨e0, e1, e2, e3⟩ := quadInt_tbQuad hq k
  have h0 := hl 0 k; have h1 := hl 1 k; have h2 := hl 2 k; have h3 := hl 3 k
  have hp : 0 ≤ pLimbI k ∧ pLimbI k < 2 ^ 44 := by fin_cases k <;> simp [pLimbI]
  simp only [InFold]
  match j with
  | 0 => rw [e0]; omega
  | 1 => rw [e1]; omega
  | 2 => rw [e2]; omega
  | 3 => rw [e3]; omega

theorem quadInt_tbF_bounds {q : Quad} (hq : QuadU44 q) (j : Fin 4) (k : Fin 6) :
    0 ≤ quadInt (tbF q) j k ∧ quadInt (tbF q) j k ≤ 2 ^ 44 - 1 := by
  rw [tbF, quadInt_foldSignedQuad _ (inFold_tb hq)]
  exact foldSignedLimb_bounds (inFold_tb hq j) k

theorem u44_tbF {q : Quad} (hq : QuadU44 q) : QuadU44 (tbF q) :=
  unn_of_quadInt (quadInt_tbF_bounds hq)

theorem elemZ_tbF {q : Quad} (hq : QuadU44 q) (j : Fin 4) :
    elemZ (quadLimb (tbF q).v03 (tbF q).v14 (tbF q).v25 j)
      = ((decodeNat (quadInt (tbQuad q) j) : ℤ) : ZMod p) := by
  rw [elemZ_of_int (quadLimb_eq_quadInt (fun j k => (quadInt_tbF_bounds hq j k).1) j),
    show quadInt (tbF q) j = foldSignedLimb (quadInt (tbQuad q) j)
      from funext (quadInt_foldSignedQuad _ (inFold_tb hq) j), decodeNat_foldSignedLimb_zmod]

/-- An element's value from its limbs, as a `decodeNat` over `ℤ`. -/
theorem quadElem_int (q : Quad) (j : Fin 4) :
    quadElem q j = ((decodeNat (fun k => (quadLimb q.v03 q.v14 q.v25 j k : ℤ)) : ℤ) : ZMod p) :=
  (quadElem_eq q j).trans (elemZ_of_int fun _ => rfl)

theorem pLimbI_zmod : ((decodeNat pLimbI : ℤ) : ZMod p) = 0 := by
  rw [decodeNat_pLimbI]; simp

/-- `a`'s lanes in the field: `(Y - X, X + Y, 2Z, T)`. -/
theorem zmod_tb {q : Quad} (hq : QuadU44 q) :
    ((decodeNat (quadInt (tbQuad q) 0) : ℤ) : ZMod p) = quadElem q 1 - quadElem q 0
      ∧ ((decodeNat (quadInt (tbQuad q) 1) : ℤ) : ZMod p) = quadElem q 0 + quadElem q 1
      ∧ ((decodeNat (quadInt (tbQuad q) 2) : ℤ) : ZMod p) = quadElem q 2 + quadElem q 2
      ∧ ((decodeNat (quadInt (tbQuad q) 3) : ℤ) : ZMod p) = quadElem q 3 := by
  have hP := pLimbI_zmod
  simp only [quadElem_int]
  have e : ∀ j, quadInt (tbQuad q) j = fun k => quadInt (tbQuad q) j k := fun _ => rfl
  rw [e 0, e 1, e 2, e 3]
  simp only [fun k => (quadInt_tbQuad hq k).1, fun k => (quadInt_tbQuad hq k).2.1,
    fun k => (quadInt_tbQuad hq k).2.2.1, fun k => (quadInt_tbQuad hq k).2.2.2]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [← sub_eq_zero, ← hP]; simp only [decodeNat_eq]; push_cast; ring_nf; done)
    | (simp only [decodeNat_eq] <;> push_cast <;> ring_nf)

/-! ## The first multiply -/

theorem u44_addA {a b : Quad} (ha : QuadU44 a) (hb : QuadU44 b) : QuadU44 (addA a b) := by
  have hT := u44_tbF ha
  refine unn_of_quadLimb (by omega) fun j k => ?_
  rw [← vectorFunc_eq, addA, laneFunc_foldQuad]
  refine foldLimb_lt (fun i => ?_) k
  rw [vectorFunc_eq, quadMul_limbs _ _ (u47_of_u44 hb.1) (u47_of_u44 hb.2.1) (u47_of_u44 hb.2.2)
    (u47_of_u44 hT.1) (u47_of_u44 hT.2.1) (u47_of_u44 hT.2.2)]
  have := quadMulLimb_lt_u44 _ _ hb.1 hb.2.1 hb.2.2 hT.1 hT.2.1 hT.2.2 j i
  omega

theorem quadElem_addA {a b : Quad} (ha : QuadU44 a) (hb : QuadU44 b) (j : Fin 4) :
    quadElem (addA a b) j
      = quadElem b j * ((decodeNat (quadInt (tbQuad a) j) : ℤ) : ZMod p) := by
  have hT := u44_tbF ha
  rw [addA, quadElem_foldQuad, quadElem_eq,
    show quadLimb _ _ _ j = quadMulLimb b (tbF a) j from
      funext (quadMul_limbs _ _ (u47_of_u44 hb.1) (u47_of_u44 hb.2.1) (u47_of_u44 hb.2.2)
        (u47_of_u44 hT.1) (u47_of_u44 hT.2.1) (u47_of_u44 hT.2.2) j),
    elemZ, quadMul_zmod, laneFunc_vector, laneFunc_vector, ← elemZ_tbF ha, quadElem_eq]

/-! ## `(E, H, G, F)` -/

theorem quadInt_ehgfQuad {q : Quad} (hq : QuadU44 q) (k : Fin 6) :
    quadInt (ehgfQuad q) 0 k
        = (quadLimb q.v03 q.v14 q.v25 1 k : ℤ) - quadLimb q.v03 q.v14 q.v25 0 k + pLimbI k
      ∧ quadInt (ehgfQuad q) 1 k
        = (quadLimb q.v03 q.v14 q.v25 0 k : ℤ) + quadLimb q.v03 q.v14 q.v25 1 k
      ∧ quadInt (ehgfQuad q) 2 k
        = (quadLimb q.v03 q.v14 q.v25 3 k : ℤ) + quadLimb q.v03 q.v14 q.v25 2 k
      ∧ quadInt (ehgfQuad q) 3 k
        = (quadLimb q.v03 q.v14 q.v25 2 k : ℤ) - quadLimb q.v03 q.v14 q.v25 3 k + pLimbI k := by
  obtain ⟨b03, b14, b25⟩ := lanes61 hq
  fin_cases k <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [quadInt, vlaneInt, ehgfQuad, ehgfVec, quadLimb, vlane, pLimbI,
      Fin.reduceCastAdd, Fin.reduceAddNat, Fin.isValue,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] <;>
    first
    | (rw [toInt_sub_add_ofNat (b03 _ _) (b03 _ _)] <;> norm_num)
    | (rw [toInt_sub_add_ofNat (b14 _ _) (b14 _ _)] <;> norm_num)
    | (rw [toInt_sub_add_ofNat (b25 _ _) (b25 _ _)] <;> norm_num)
    | rw [toInt_add_lt (b03 _ _) (b03 _ _)]
    | rw [toInt_add_lt (b14 _ _) (b14 _ _)]
    | rw [toInt_add_lt (b25 _ _) (b25 _ _)]

theorem inFold_ehgf {q : Quad} (hq : QuadU44 q) (j : Fin 4) (k : Fin 6) :
    InFold (quadInt (ehgfQuad q) j k) := by
  have hl := quadLimb_lt q 44 (by omega) hq.1 hq.2.1 hq.2.2
  obtain ⟨e0, e1, e2, e3⟩ := quadInt_ehgfQuad hq k
  have h0 := hl 0 k; have h1 := hl 1 k; have h2 := hl 2 k; have h3 := hl 3 k
  have hp : 0 ≤ pLimbI k ∧ pLimbI k < 2 ^ 44 := by fin_cases k <;> simp [pLimbI]
  simp only [InFold]
  match j with
  | 0 => rw [e0]; omega
  | 1 => rw [e1]; omega
  | 2 => rw [e2]; omega
  | 3 => rw [e3]; omega

/-- `(E, H, G, F)` in the field, over `(A, B, D, C)`. -/
theorem zmod_ehgf {q : Quad} (hq : QuadU44 q) :
    ((decodeNat (quadInt (ehgfQuad q) 0) : ℤ) : ZMod p) = quadElem q 1 - quadElem q 0
      ∧ ((decodeNat (quadInt (ehgfQuad q) 1) : ℤ) : ZMod p) = quadElem q 0 + quadElem q 1
      ∧ ((decodeNat (quadInt (ehgfQuad q) 2) : ℤ) : ZMod p) = quadElem q 3 + quadElem q 2
      ∧ ((decodeNat (quadInt (ehgfQuad q) 3) : ℤ) : ZMod p) = quadElem q 2 - quadElem q 3 := by
  have hP := pLimbI_zmod
  simp only [quadElem_int]
  have e : ∀ j, quadInt (ehgfQuad q) j = fun k => quadInt (ehgfQuad q) j k := fun _ => rfl
  rw [e 0, e 1, e 2, e 3]
  simp only [fun k => (quadInt_ehgfQuad hq k).1, fun k => (quadInt_ehgfQuad hq k).2.1,
    fun k => (quadInt_ehgfQuad hq k).2.2.1, fun k => (quadInt_ehgfQuad hq k).2.2.2]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [← sub_eq_zero, ← hP]; simp only [decodeNat_eq]; push_cast; ring_nf; done)
    | (simp only [decodeNat_eq]; push_cast; ring_nf)

theorem quadInt_addR_bounds {a b : Quad} (ha : QuadU44 a) (hb : QuadU44 b) (j : Fin 4)
    (k : Fin 6) : 0 ≤ quadInt (addR a b) j k ∧ quadInt (addR a b) j k ≤ 2 ^ 44 - 1 := by
  rw [addR, quadInt_foldSignedQuad _ (inFold_ehgf (u44_addA ha hb))]
  exact foldSignedLimb_bounds (inFold_ehgf (u44_addA ha hb) j) k

theorem u44_addR {a b : Quad} (ha : QuadU44 a) (hb : QuadU44 b) : QuadU44 (addR a b) :=
  unn_of_quadInt (quadInt_addR_bounds ha hb)

theorem elemZ_addR {a b : Quad} (ha : QuadU44 a) (hb : QuadU44 b) (j : Fin 4) :
    elemZ (quadLimb (addR a b).v03 (addR a b).v14 (addR a b).v25 j)
      = ((decodeNat (quadInt (ehgfQuad (addA a b)) j) : ℤ) : ZMod p) := by
  rw [elemZ_of_int (quadLimb_eq_quadInt (fun j k => (quadInt_addR_bounds ha hb j k).1) j),
    show quadInt (addR a b) j = foldSignedLimb (quadInt (ehgfQuad (addA a b)) j)
      from funext (quadInt_foldSignedQuad _ (inFold_ehgf (u44_addA ha hb)) j),
    decodeNat_foldSignedLimb_zmod]

/-! ## The second multiply -/

private theorem unn_permEGGE {n : ℕ} {v : Vector (BitVec 64) 8} (h : R43x6.UNN n v) :
    R43x6.UNN n (permEGGE v) := by
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i
  all_goals first
    | exact h.1 0 | exact h.1 2 | exact h.1 4 | exact h.1 6
    | exact h.2 0 | exact h.2 2 | exact h.2 4 | exact h.2 6

private theorem unn_permFHFH {n : ℕ} {v : Vector (BitVec 64) 8} (h : R43x6.UNN n v) :
    R43x6.UNN n (permFHFH v) := by
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i
  all_goals first
    | exact h.1 1 | exact h.1 3 | exact h.1 5 | exact h.1 7
    | exact h.2 1 | exact h.2 3 | exact h.2 5 | exact h.2 7

theorem u44_egegQuad {r : Quad} (h : QuadU44 r) : QuadU44 (egegQuad r) :=
  ⟨unn_permEGGE h.1, unn_permEGGE h.2.1, unn_permEGGE h.2.2⟩

theorem u44_fhfhQuad {r : Quad} (h : QuadU44 r) : QuadU44 (fhfhQuad r) :=
  ⟨unn_permFHFH h.1, unn_permFHFH h.2.1, unn_permFHFH h.2.2⟩

/-- **`u44` in, `u44` out.** -/
theorem u44_geAddTable {a b : Quad} (ha : QuadU44 a) (hb : QuadU44 b) :
    QuadU44 (geAddTable a b) := by
  have hR := u44_addR ha hb
  have hG := u44_egegQuad hR
  have hF := u44_fhfhQuad hR
  refine unn_of_quadLimb (by omega) fun j k => ?_
  rw [← vectorFunc_eq, geAddTable, laneFunc_foldQuad]
  refine foldLimb_lt (fun i => ?_) k
  rw [vectorFunc_eq, quadMul_limbs _ _ (u47_of_u44 hG.1) (u47_of_u44 hG.2.1) (u47_of_u44 hG.2.2)
    (u47_of_u44 hF.1) (u47_of_u44 hF.2.1) (u47_of_u44 hF.2.2)]
  have := quadMulLimb_lt_u44 _ _ hG.1 hG.2.1 hG.2.2 hF.1 hF.2.1 hF.2.2 j i
  omega

theorem quadLimb_egegQuad (r : Quad) :
    let e := egegQuad r
    quadLimb e.v03 e.v14 e.v25 0 = quadLimb r.v03 r.v14 r.v25 0
      ∧ quadLimb e.v03 e.v14 e.v25 1 = quadLimb r.v03 r.v14 r.v25 2
      ∧ quadLimb e.v03 e.v14 e.v25 2 = quadLimb r.v03 r.v14 r.v25 2
      ∧ quadLimb e.v03 e.v14 e.v25 3 = quadLimb r.v03 r.v14 r.v25 0 := by
  refine ⟨funext fun k => ?_, funext fun k => ?_, funext fun k => ?_, funext fun k => ?_⟩ <;>
    fin_cases k <;> rfl

theorem quadLimb_fhfhQuad (r : Quad) :
    let f := fhfhQuad r
    quadLimb f.v03 f.v14 f.v25 0 = quadLimb r.v03 r.v14 r.v25 3
      ∧ quadLimb f.v03 f.v14 f.v25 1 = quadLimb r.v03 r.v14 r.v25 1
      ∧ quadLimb f.v03 f.v14 f.v25 2 = quadLimb r.v03 r.v14 r.v25 3
      ∧ quadLimb f.v03 f.v14 f.v25 3 = quadLimb r.v03 r.v14 r.v25 1 := by
  refine ⟨funext fun k => ?_, funext fun k => ?_, funext fun k => ?_, funext fun k => ?_⟩ <;>
    fin_cases k <;> rfl

theorem quadElem_geAddTable {a b : Quad} (ha : QuadU44 a) (hb : QuadU44 b) (j : Fin 4) :
    quadElem (geAddTable a b) j
      = elemZ (quadLimb (egegQuad (addR a b)).v03 (egegQuad (addR a b)).v14
          (egegQuad (addR a b)).v25 j)
        * elemZ (quadLimb (fhfhQuad (addR a b)).v03 (fhfhQuad (addR a b)).v14
            (fhfhQuad (addR a b)).v25 j) := by
  have hR := u44_addR ha hb
  have hG := u44_egegQuad hR
  have hF := u44_fhfhQuad hR
  rw [geAddTable, quadElem_foldQuad, quadElem_eq,
    show quadLimb _ _ _ j = quadMulLimb (egegQuad (addR a b)) (fhfhQuad (addR a b)) j from
      funext (quadMul_limbs _ _ (u47_of_u44 hG.1) (u47_of_u44 hG.2.1) (u47_of_u44 hG.2.2)
        (u47_of_u44 hF.1) (u47_of_u44 hF.2.1) (u47_of_u44 hF.2.2) j),
    elemZ, quadMul_zmod, laneFunc_vector, laneFunc_vector]

/-- **`FD_R43X6_GE_ADD_TABLE_ALT` adds**: the point is `Point.addPrecomputed` of `a`'s and the
table point's. -/
theorem toPoint_geAddTable {a b : Quad} (ha : QuadU44 a) (hb : QuadU44 b) :
    (geAddTable a b).toPoint = a.toPoint.addPrecomputed (PrecomputedPoint.ofSlots b.toPoint) := by
  obtain ⟨g0, g1, g2, g3⟩ := quadLimb_egegQuad (addR a b)
  obtain ⟨f0, f1, f2, f3⟩ := quadLimb_fhfhQuad (addR a b)
  obtain ⟨p0, p1, p2, p3⟩ := zmod_ehgf (u44_addA ha hb)
  obtain ⟨t0, t1, t2, t3⟩ := zmod_tb ha
  have e0 := quadElem_geAddTable ha hb 0
  have e1 := quadElem_geAddTable ha hb 1
  have e2 := quadElem_geAddTable ha hb 2
  have e3 := quadElem_geAddTable ha hb 3
  rw [g0, f0, elemZ_addR ha hb, elemZ_addR ha hb, p0, p3] at e0
  rw [g1, f1, elemZ_addR ha hb, elemZ_addR ha hb, p2, p1] at e1
  rw [g2, f2, elemZ_addR ha hb, elemZ_addR ha hb, p2, p3] at e2
  rw [g3, f3, elemZ_addR ha hb, elemZ_addR ha hb, p0, p1] at e3
  simp only [quadElem_addA ha hb, t0, t1, t2, t3] at e0 e1 e2 e3
  show Point.mk (quadElem (geAddTable a b) 0) (quadElem (geAddTable a b) 1)
      (quadElem (geAddTable a b) 2) (quadElem (geAddTable a b) 3)
    = Point.addPrecomputed ⟨quadElem a 0, quadElem a 1, quadElem a 2, quadElem a 3⟩
      (PrecomputedPoint.ofSlots ⟨quadElem b 0, quadElem b 1, quadElem b 2, quadElem b 3⟩)
  rw [e0, e1, e2, e3]
  simp only [Point.addPrecomputed, PrecomputedPoint.ofSlots, Point.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

end PointAdd

end Firedancer.Avx512

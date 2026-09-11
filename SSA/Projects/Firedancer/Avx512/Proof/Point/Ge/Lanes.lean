/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Proof.Point.Ge.Model

/-!
# Lane operations and the fold runs

Each `denote_*` lemma takes the `denote_eval` hypotheses of one run of
instructions and names the vector they leave by its model definition.
Hypotheses are stated through `vbin`/`vshuf`: written out as `Vector.ofFn`, a
chain of a dozen of them elaborates in exponential time.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

namespace Ge

/-! ## Lane operations on values -/

theorem add_value (a b : BitVec 64) : LLVM.add (.value a) (.value b) = .value (a + b) := rfl
theorem sub_value (a b : BitVec 64) : LLVM.sub (.value a) (.value b) = .value (a - b) := rfl
theorem and_value (a b : BitVec 64) : LLVM.and (.value a) (.value b) = .value (a &&& b) := rfl
theorem mul_value (a b : BitVec 64) : LLVM.mul (.value a) (.value b) = .value (a * b) := rfl
theorem mul_poison (x : LLVM.IntW 64) : LLVM.mul x .poison = .poison := by
  rcases x with ⟨_ | _⟩ <;> rfl
theorem add_poison (x : LLVM.IntW 64) : LLVM.add x .poison = .poison := by
  rcases x with ⟨_ | _⟩ <;> rfl

theorem add_value_of_lt {a b : BitVec 64} (fs : LLVM.NoWrapFlags)
    (h : a.toNat + b.toNat < 2 ^ 63) : LLVM.add (.value a) (.value b) fs = .value (a + b) := by
  simp [LLVM.add, Firedancer.saddOverflow_eq_false h,
    Firedancer.uaddOverflow_eq_false (show a.toNat + b.toNat < 2 ^ 64 by omega), LLVM.add?]

theorem shl_value0 (a : BitVec 64) : LLVM.shl (.value a) (.value 0#64) = .value a := by
  simp [LLVM.shl, LLVM.shl?]

theorem shl_value1 (a : BitVec 64) : LLVM.shl (.value a) (.value 1#64) = .value (a + a) := by
  simp only [LLVM.shl, LLVM.shl?, PoisonOr.value_bind, Bool.false_eq_true, false_and, if_false]
  rw [if_neg (by decide)]
  congr 1
  bv_decide

theorem ashr_value {n : ℕ} (a : BitVec 64) (hn : n < 64) :
    LLVM.ashr (.value a) (.value (BitVec.ofNat 64 n)) = .value (a.sshiftRight n) := by
  simp only [LLVM.ashr, LLVM.ashr?, PoisonOr.value_bind, Bool.false_eq_true, false_and, if_false]
  rw [if_neg (by rw [ge_iff_le, BitVec.le_def]; simp; omega),
    BitVec.sshiftRight'_ofNat_eq_sshiftRight, Nat.mod_eq_of_lt (by omega)]

theorem add_value_of_lt62 {a b : BitVec 64} (fs : LLVM.NoWrapFlags)
    (ha : a.toNat < 2 ^ 62) (hb : b.toNat < 2 ^ 62) :
    LLVM.add (.value a) (.value b) fs = .value (a + b) :=
  add_value_of_lt fs (by omega)

/-! ## Runs -/

/-- A lanewise vector operation, as `denote_eval` leaves one. -/
def vbin (op : InstCombine.MOp.BinaryOp) (a b : Vector (LLVM.IntW 64) 8) :
    Vector (LLVM.IntW 64) 8 :=
  Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote op a[i.val] b[i.val]

/-- A `shufflevector` on `vector<8xi64>`. -/
def vshuf (mask : List Int) (a b : Vector (LLVM.IntW 64) 8) :
    Vector (LLVM.IntW 64) mask.length :=
  LLVM.Ty.shufflevector (e := .bitvec (.concrete 64)) mask a b

/-- `simp only` over one lane of a vector run: indexing, shuffles, the lane
operations. Extra lemmas through the argument. -/
syntax "ge_lane_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| ge_lane_simp $[[$ls,*]]?) => do
    let ls := ls.map (·.getElems) |>.getD #[]
    `(tactic| simp only [vbin, vshuf, LLVM.Ty.shufflevector, Vector.getElem_ofFn,
      Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, List.getD_cons_zero, List.getD_cons_succ, Int.reduceLT,
      Int.reduceToNat, Nat.reduceLT, Nat.reduceSub, dite_true, dite_false, ite_false, ite_true,
      Bool.false_eq_true, decide_false, decide_true, reduceIte, reduceDIte,
      InstCombine.binaryDenote, toBitVecValue, Fin.isValue, List.length_cons, List.length_nil,
      Nat.reduceAdd, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, $ls,*])

/-- Lanewise: `Vector.ext`, one goal per lane, `ge_lane_simp`, and `rfl` for what is left. -/
macro "ge_lanes" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (apply Vector.ext; intro i hi
             simp only [List.length_cons, List.length_nil] at hi
             interval_cases i <;> ge_lane_simp [$ls,*] <;> try rfl))

/-- `p`'s limbs on lanes 0 and 4, poison elsewhere. -/
def pmaskE (c d : BitVec 64) : Vector (LLVM.IntW 64) 8 :=
  #v[.value c, .poison, .poison, .poison, .value d, .poison, .poison, .poison]

/-! ## The signed fold -/

/-- The negated bias `QUAD_FOLD_SIGNED` adds to the `03` vector. -/
def nbias03 : Vector Nat 8 :=
  #v[18446744073550168064, 18446744073550168064, 18446744073550168064, 18446744073550168064,
     18446744073708503040, 18446744073708503040, 18446744073708503040, 18446744073708503040]

/-- ... to the `14` and `25` vectors. -/
def nbias : Vector Nat 8 :=
  #v[18446744073708503040, 18446744073708503040, 18446744073708503040, 18446744073708503040,
     18446744073708503040, 18446744073708503040, 18446744073708503040, 18446744073708503040]

/-- The bias added back to `03`. -/
def bias03 : Vector Nat 8 :=
  #v[159383552, 159383552, 159383552, 159383552, 1048576, 1048576, 1048576, 1048576]

/-- ... to `14` and `25`. -/
def bias : Vector Nat 8 :=
  #v[1048576, 1048576, 1048576, 1048576, 1048576, 1048576, 1048576, 1048576]

private theorem toNat_and_le (x m : BitVec 64) : (x &&& m).toNat ≤ m.toNat := by
  simp only [BitVec.toNat_and]; exact Nat.and_le_right

/-- A masked lane plus the bias. -/
theorem add_and_bias {x m : BitVec 64} {c : ℕ} (fs : LLVM.NoWrapFlags) (hm : m.toNat < 2 ^ 44)
    (hc : c < 2 ^ 44) :
    LLVM.add (.value (x &&& m)) (.value (BitVec.ofNat 64 c)) fs
      = .value ((x &&& m) + BitVec.ofNat 64 c) :=
  add_value_of_lt fs (by
    have := toNat_and_le x m
    simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]; omega)

theorem sshr43_bounds (x : BitVec 64) :
    -2 ^ 20 ≤ (x.sshiftRight 43).toInt ∧ (x.sshiftRight 43).toInt < 2 ^ 20 := by
  have e : (x.sshiftRight 43).toInt = x.toInt / 2 ^ 43 := by
    rw [BitVec.toInt_sshiftRight, R43x6.shiftRight_eq]
  have h1 := BitVec.toInt_lt (x := x)
  have h2 := BitVec.le_toInt (x := x)
  norm_num at h1 h2
  rw [e]
  constructor
  · apply Int.le_ediv_of_mul_le (by norm_num); omega
  · apply Int.ediv_lt_of_lt_mul (by norm_num); omega

/-- A carry plus the bias, `nsw`: a carry is in `[-2^20, 2^20)`. -/
theorem add_sshr_bias (x : BitVec 64) (fs : LLVM.NoWrapFlags) (hfs : fs.nuw = false) :
    LLVM.add (.value (x.sshiftRight 43)) (.value 1048576#64) fs
      = .value (x.sshiftRight 43 + 1048576#64) := by
  have hb := sshr43_bounds x
  have hs : (x.sshiftRight 43).saddOverflow 1048576#64 = false := by
    simp only [BitVec.saddOverflow, show (1048576#64 : BitVec 64).toInt = 1048576 from rfl,
      show (2 : ℤ) ^ (64 - 1) = 9223372036854775808 by norm_num, Bool.or_eq_false_iff,
      decide_eq_false_iff_not]
    omega
  simp [LLVM.add, hs, hfs, LLVM.add?]

/-- ... and the biased carry is below `2^21`. -/
theorem toNat_sshr_bias (x : BitVec 64) : (x.sshiftRight 43 + 1048576#64).toNat < 2 ^ 21 := by
  have hb := sshr43_bounds x
  have e : x.sshiftRight 43 + 1048576#64
      = BitVec.ofInt 64 ((x.sshiftRight 43).toInt + 1048576) := by
    rw [BitVec.ofInt_add, ofInt_toInt]; rfl
  have h := toNat_ofInt (a := (x.sshiftRight 43).toInt + 1048576)
    (by simp only [R43x6.FitsLong]; omega) (by omega)
  rw [e]
  omega

/-- The biased carry plus a masked lane. -/
theorem add_bias_and {x y m : BitVec 64} (fs : LLVM.NoWrapFlags) (hm : m.toNat < 2 ^ 44) :
    LLVM.add (.value (x.sshiftRight 43 + 1048576#64)) (.value (y &&& m)) fs
      = .value (x.sshiftRight 43 + 1048576#64 + (y &&& m)) :=
  add_value_of_lt fs (by have := toNat_sshr_bias x; have := toNat_and_le y m; omega)

/-- `x` with the negated `03` bias. -/
def nb03v (x : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  #v[x[0] + 18446744073550168064#64, x[1] + 18446744073550168064#64,
     x[2] + 18446744073550168064#64, x[3] + 18446744073550168064#64,
     x[4] + 18446744073708503040#64, x[5] + 18446744073708503040#64,
     x[6] + 18446744073708503040#64, x[7] + 18446744073708503040#64]

/-- `x` with the negated `14`/`25` bias. -/
def nbv (x : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  #v[x[0] + 18446744073708503040#64, x[1] + 18446744073708503040#64,
     x[2] + 18446744073708503040#64, x[3] + 18446744073708503040#64,
     x[4] + 18446744073708503040#64, x[5] + 18446744073708503040#64,
     x[6] + 18446744073708503040#64, x[7] + 18446744073708503040#64]

theorem denote_nb03v {x : Vector (BitVec 64) 8} {c a : Vector (LLVM.IntW 64) 8}
    (hc : c = toBitVecValue 64 nbias03) (h : a = vbin .add (x.map PoisonOr.value) c) :
    a = (nb03v x).map PoisonOr.value := by
  subst hc h; ge_lanes [nbias03, nb03v, add_value]

theorem denote_nbv {x : Vector (BitVec 64) 8} {c a : Vector (LLVM.IntW 64) 8}
    (hc : c = toBitVecValue 64 nbias) (h : a = vbin .add (x.map PoisonOr.value) c) :
    a = (nbv x).map PoisonOr.value := by
  subst hc h; ge_lanes [nbias, nbv, add_value]

/-- **`FD_R43X6_QUAD_FOLD_SIGNED`'s `03`.** -/
theorem denote_foldSigned03 {P : Quad}
    {c111 c112 c114 c132 c133 c134 : Vector (LLVM.IntW 64) 8}
    (hc111 : c111 = toBitVecValue 64 nbias03) (hc112 : c112 = toBitVecValue 64 nbias)
    (hc114 : c114 = toBitVecValue 64 quadShift48) (hc132 : c132 = quadMul19)
    (hc133 : c133 = toBitVecValue 64 quadMask43) (hc134 : c134 = toBitVecValue 64 bias03)
    {a206 a208 a211 a212 a213 a214 a215 a216 : Vector (LLVM.IntW 64) 8}
    (h206 : a206 = vbin .add (P.v03.map PoisonOr.value) c111)
    (h208 : a208 = vbin .add (P.v25.map PoisonOr.value) c112)
    (h211 : a211 = vbin .ashr a208 c114)
    (h212 : a212 = vbin .mul a211 c132)
    (h213 : a213 = vbin .and a206 c133)
    (h214 : a214 = vshuf [4, 5, 6, 7, 8, 9, 10, 11] a212 a211)
    (h215 : a215 = vbin (.add { nsw := true, nuw := true }) a213 c134)
    (h216 : a216 = vbin .add a215 a214) :
    a216 = (foldSignedQuad P).v03.map PoisonOr.value := by
  replace h206 := denote_nb03v hc111 h206
  replace h208 := denote_nbv hc112 h208
  subst hc114 hc132 hc133 hc134 h206 h208
  replace h211 : a211 = (#v[(nbv P.v25)[0].sshiftRight 43, (nbv P.v25)[1].sshiftRight 43,
      (nbv P.v25)[2].sshiftRight 43, (nbv P.v25)[3].sshiftRight 43,
      (nbv P.v25)[4].sshiftRight 40, (nbv P.v25)[5].sshiftRight 40,
      (nbv P.v25)[6].sshiftRight 40, (nbv P.v25)[7].sshiftRight 40]
      : Vector (BitVec 64) 8).map PoisonOr.value := by
    subst h211; ge_lanes [quadShift48, ashr_value]
  subst h211 h212 h213 h214 h215 h216
  ge_lanes [quadMul19, mul_value, mul_poison, quadMask43, and_value, bias03, add_value,
    add_and_bias, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, foldSignedQuad, fsL0, fsL3,
    nb03v, nbv]

/-- **`FD_R43X6_QUAD_FOLD_SIGNED`'s `14`.** -/
theorem denote_foldSigned14 {P : Quad} {c111 c112 c113 c133 c135 : Vector (LLVM.IntW 64) 8}
    (hc111 : c111 = toBitVecValue 64 nbias03) (hc112 : c112 = toBitVecValue 64 nbias)
    (hc113 : c113 = toBitVecValue 64 quadShift43) (hc133 : c133 = toBitVecValue 64 quadMask43)
    (hc135 : c135 = toBitVecValue 64 bias)
    {a206 a207 a209 a217 a218 a219 : Vector (LLVM.IntW 64) 8}
    (h206 : a206 = vbin .add (P.v03.map PoisonOr.value) c111)
    (h207 : a207 = vbin .add (P.v14.map PoisonOr.value) c112)
    (h209 : a209 = vbin .ashr a206 c113)
    (h217 : a217 = vbin .and a207 c133)
    (h218 : a218 = vbin (.add { nsw := true }) a209 c135)
    (h219 : a219 = vbin (.add { nsw := true }) a218 a217) :
    a219 = (foldSignedQuad P).v14.map PoisonOr.value := by
  replace h206 := denote_nb03v hc111 h206
  replace h207 := denote_nbv hc112 h207
  subst hc113 hc133 hc135 h206 h207 h209 h217 h218 h219
  ge_lanes [quadShift43, ashr_value, quadMask43, and_value, bias, add_sshr_bias, add_bias_and,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, eq_self_iff_true, foldSignedQuad, fsMid,
    nb03v, nbv]

/-- **`FD_R43X6_QUAD_FOLD_SIGNED`'s `25`.** -/
theorem denote_foldSigned25 {P : Quad} {c112 c113 c135 c136 : Vector (LLVM.IntW 64) 8}
    (hc112 : c112 = toBitVecValue 64 nbias) (hc113 : c113 = toBitVecValue 64 quadShift43)
    (hc135 : c135 = toBitVecValue 64 bias) (hc136 : c136 = toBitVecValue 64 quadMask48)
    {a207 a208 a210 a220 a221 a222 : Vector (LLVM.IntW 64) 8}
    (h207 : a207 = vbin .add (P.v14.map PoisonOr.value) c112)
    (h208 : a208 = vbin .add (P.v25.map PoisonOr.value) c112)
    (h210 : a210 = vbin .ashr a207 c113)
    (h220 : a220 = vbin .and a208 c136)
    (h221 : a221 = vbin (.add { nsw := true }) a210 c135)
    (h222 : a222 = vbin (.add { nsw := true }) a221 a220) :
    a222 = (foldSignedQuad P).v25.map PoisonOr.value := by
  replace h207 := denote_nbv hc112 h207
  replace h208 := denote_nbv hc112 h208
  subst hc113 hc135 hc136 h207 h208 h210 h220 h221 h222
  ge_lanes [quadShift43, ashr_value, quadMask48, and_value, bias, add_sshr_bias, add_bias_and,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, eq_self_iff_true, foldSignedQuad, fsMid,
    nbv]

/-! ## The unsigned fold -/

/-- `FD_R43X6_QUAD_FOLD_UNSIGNED`'s `03`: `Quad.lean`'s lemma through `vbin`. -/
theorem denote_foldU03 {q : Quad} {c114 c132 c133 : Vector (LLVM.IntW 64) 8}
    (hc114 : c114 = toBitVecValue 64 quadShift48) (hc132 : c132 = quadMul19)
    (hc133 : c133 = toBitVecValue 64 quadMask43)
    {a286 a287 a288 a289 a290 : Vector (LLVM.IntW 64) 8}
    (h286 : a286 = vbin .lshr (q.v25.map PoisonOr.value) c114)
    (h287 : a287 = vbin (.mul { nsw := true, nuw := true }) a286 c132)
    (h288 : a288 = vbin .and (q.v03.map PoisonOr.value) c133)
    (h289 : a289 = vshuf [4, 5, 6, 7, 8, 9, 10, 11] a287 a286)
    (h290 : a290 = vbin (.add { nsw := true, nuw := true }) a289 a288) :
    a290 = (foldQuad q).v03.map PoisonOr.value := by
  subst hc114 hc132 hc133
  exact denote_quadFold_v03 h286 h287 h288 h289 h290

theorem denote_foldU14 {q : Quad} {c113 c133 : Vector (LLVM.IntW 64) 8}
    (hc113 : c113 = toBitVecValue 64 quadShift43) (hc133 : c133 = toBitVecValue 64 quadMask43)
    {a282 a292 a293 : Vector (LLVM.IntW 64) 8}
    (h282 : a282 = vbin .lshr (q.v03.map PoisonOr.value) c113)
    (h292 : a292 = vbin .and (q.v14.map PoisonOr.value) c133)
    (h293 : a293 = vbin (.add { nsw := true, nuw := true }) a292 a282) :
    a293 = (foldQuad q).v14.map PoisonOr.value := by
  subst hc113 hc133
  exact denote_quadFold_v14 h282 h292 h293

theorem denote_foldU25 {q : Quad} {c113 c136 : Vector (LLVM.IntW 64) 8}
    (hc113 : c113 = toBitVecValue 64 quadShift43) (hc136 : c136 = toBitVecValue 64 quadMask48)
    {a284 a295 a296 : Vector (LLVM.IntW 64) 8}
    (h284 : a284 = vbin .lshr (q.v14.map PoisonOr.value) c113)
    (h295 : a295 = vbin .and (q.v25.map PoisonOr.value) c136)
    (h296 : a296 = vbin (.add { nsw := true, nuw := true }) a295 a284) :
    a296 = (foldQuad q).v25.map PoisonOr.value := by
  subst hc113 hc136
  exact denote_quadFold_v25 h284 h295 h296

end Ge

end Firedancer.Avx512

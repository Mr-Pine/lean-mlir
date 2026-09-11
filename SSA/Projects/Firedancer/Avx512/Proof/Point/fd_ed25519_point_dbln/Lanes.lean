/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_dbln.Model
import SSA.Projects.Firedancer.Avx512.Proof.Point.Ge.Lanes

/-!
# `FD_R43X6_GE_DBL`'s instruction runs, reduced to the model

Each lemma takes the `denote_eval` hypotheses of one run of instructions and
names the vector they leave by its `PointDbln` definition; the walks of `^bb0`
and `^bb3` both apply them.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

namespace PointDbln
open Ge

/-! ## The runs -/

/-- **`%151`/`%158`/`%159`**: `(X+Y, Y, Z, X)`. The `add` is `nsw` in `^bb3`; on
`u44` lanes nothing overflows. -/
theorem denote_addXY {x : Vector (BitVec 64) 8} {fs : LLVM.NoWrapFlags}
    {z a b c : Vector (LLVM.IntW 64) 8} (hx : R43x6.U44 x)
    (ha : a = vshuf [1, 1, 2, 0, 5, 5, 6, 4] (x.map PoisonOr.value) z)
    (hb : b = vbin (.add fs) a (x.map PoisonOr.value))
    (hc : c = vshuf [0, 9, 10, 11, 4, 13, 14, 15] b a) :
    c = (addXY x).map PoisonOr.value := by
  have hl : ∀ (i : ℕ) (h : i < 8), (x[i]'h).toNat < 2 ^ 62 := fun i h => by
    have := unn_toNat x 44 (by omega) hx ⟨i, h⟩; simp only [Fin.getElem_fin] at this; omega
  replace ha : a = (#v[x[1], x[1], x[2], x[0], x[5], x[5], x[6], x[4]]
      : Vector (BitVec 64) 8).map PoisonOr.value := by subst ha; ge_lanes []
  subst ha
  replace hb : b = (#v[x[1] + x[0], x[1] + x[1], x[2] + x[2], x[0] + x[3], x[5] + x[4],
      x[5] + x[5], x[6] + x[6], x[4] + x[7]] : Vector (BitVec 64) 8).map PoisonOr.value := by
    subst hb
    apply Vector.ext; intro i hi
    interval_cases i <;> ge_lane_simp [] <;> exact add_value_of_lt62 _ (hl _ _) (hl _ _)
  subst hb hc
  ge_lanes [addXY]

/-- `%24`/`%41`/`%59`: `p`'s limbs on the lanes `G` takes. -/
def pmaskG (c d : BitVec 64) : Vector (LLVM.IntW 64) 8 :=
  #v[.poison, .value c, .value c, .poison, .poison, .value d, .value d, .poison]

/-- `%4`: the shift doubling `Z²`. -/
def dblShift : Vector Nat 8 := #v[0, 0, 1, 0, 0, 0, 1, 0]

/-- The intermediate vectors of `%167`-`%199`, over the square `s`. -/
def egT (s : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  #v[s[0], s[1], s[2] + s[2], s[3], s[4], s[5], s[6] + s[6], s[7]]
def egA (s : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  #v[s[3], s[3], s[3], s[3], s[7], s[7], s[7], s[7]]
def egB (s : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  #v[s[1], s[1], s[1], s[1], s[5], s[5], s[5], s[5]]
def egH (s : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  #v[s[3] + s[1], s[3] + s[1], s[3] + s[1], s[3] + s[1],
     s[7] + s[5], s[7] + s[5], s[7] + s[5], s[7] + s[5]]
def egH' (s : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  #v[s[3] + s[1], s[3], s[3], s[3] + s[1], s[7] + s[5], s[7], s[7], s[7] + s[5]]
def egD (s : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  #v[s[3] + s[1] - s[1], s[3] - s[1], s[3] - s[1], s[3] + s[1] - s[1],
     s[7] + s[5] - s[5], s[7] - s[5], s[7] - s[5], s[7] + s[5] - s[5]]
def egG (cc dd : BitVec 64) (s : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  #v[s[3] + s[1], s[3] - s[1] + cc, s[3] - s[1] + cc, s[3] + s[1],
     s[7] + s[5], s[7] - s[5] + dd, s[7] - s[5] + dd, s[7] + s[5]]
def egF' (cc dd : BitVec 64) (s : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  #v[s[3] + s[1], s[3] - s[1] + cc, s[3] - s[1] + cc + (s[2] + s[2]),
     s[3] + s[1], s[7] + s[5], s[7] - s[5] + dd, s[7] - s[5] + dd + (s[6] + s[6]), s[7] + s[5]]

/-- **`%167`-`%199`** on one vector: the doubled `Z²`, the lane add/sub to
`(E, G, F, H)`. `m1`/`m2` are poison exactly on the lanes the following shuffle
drops. -/
theorem denote_egfh {s : Vector (BitVec 64) 8} {cc dd : BitVec 64}
    {c4 m1 m2 z1 z2 t A B H H' D E G F F' K L P : Vector (LLVM.IntW 64) 8}
    (hc4 : c4 = toBitVecValue 64 dblShift) (hm1 : m1 = pmaskG cc dd) (hm2 : m2 = pmaskE cc dd)
    (ht : t = vbin .shl (s.map PoisonOr.value) c4)
    (hA : A = vshuf [3, 3, 3, 3, 7, 7, 7, 7] t z1)
    (hB : B = vshuf [1, 1, 1, 1, 5, 5, 5, 5] t z2)
    (hH : H = vbin .add A B)
    (hH' : H' = vshuf [0, 9, 10, 3, 4, 13, 14, 7] H A)
    (hD : D = vbin .sub H' B)
    (hE : E = vbin .add D m1)
    (hG : G = vshuf [0, 9, 10, 3, 4, 13, 14, 7] H' E)
    (hF : F = vbin .add G t)
    (hF' : F' = vshuf [0, 1, 10, 3, 4, 5, 14, 7] G F)
    (hK : K = vbin .sub F' t)
    (hL : L = vbin .add K m2)
    (hP : P = vshuf [0, 9, 10, 11, 4, 13, 14, 15] L F') :
    P = (egfh cc dd s).map PoisonOr.value := by
  subst hc4 hm1 hm2
  replace ht : t = (egT s).map PoisonOr.value := by
    subst ht; ge_lanes [egT, dblShift, shl_value0, shl_value1]
  subst ht
  replace hA : A = (egA s).map PoisonOr.value := by subst hA; ge_lanes [egT, egA]
  replace hB : B = (egB s).map PoisonOr.value := by subst hB; ge_lanes [egT, egB]
  subst hA hB
  replace hH : H = (egH s).map PoisonOr.value := by subst hH; ge_lanes [egA, egB, egH, add_value]
  subst hH
  replace hH' : H' = (egH' s).map PoisonOr.value := by subst hH'; ge_lanes [egA, egH, egH']
  subst hH'
  replace hD : D = (egD s).map PoisonOr.value := by subst hD; ge_lanes [egB, egH', egD, sub_value]
  subst hD
  replace hG : G = (egG cc dd s).map PoisonOr.value := by
    subst hE hG; ge_lanes [egH', egD, egG, pmaskG, add_value, add_poison]
  subst hG
  replace hF' : F' = (egF' cc dd s).map PoisonOr.value := by
    subst hF hF'; ge_lanes [egT, egG, egF', add_value]
  subst hF' hK hL hP
  ge_lanes [egT, egF', pmaskE, add_value, sub_value, add_poison, egfh]

/-! ## Permutes -/

theorem denote_permGE {v : Vector (BitVec 64) 8} {z a : Vector (LLVM.IntW 64) 8}
    (h : a = vshuf [0, 1, 1, 0, 4, 5, 5, 4] (v.map PoisonOr.value) z) :
    a = (permGE v).map PoisonOr.value := by
  subst h; ge_lanes [permGE]

theorem denote_permFH {v : Vector (BitVec 64) 8} {z a : Vector (LLVM.IntW 64) 8}
    (h : a = vshuf [2, 3, 2, 3, 6, 7, 6, 7] (v.map PoisonOr.value) z) :
    a = (permFH v).map PoisonOr.value := by
  subst h; ge_lanes [permFH]


end PointDbln

end Firedancer.Avx512

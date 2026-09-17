/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_add_with_opts.Model
public import SSA.Projects.Firedancer.Avx512.Proof.Point.Ge.Lanes

/-!
# `FD_R43X6_GE_ADD_TABLE_ALT`'s instruction runs, reduced to the model

The runs every `GE` macro shares are `Ge`'s; these are the rest. The second signed
fold adds its bias in a different order on the `03` and `14` vectors, so it gets
its own two lemmas.
-/

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

namespace PointAdd
open Ge

/-! ## Lane operations with `nsw` -/

private theorem pow63 : (2 : ℤ) ^ (64 - 1) = 9223372036854775808 := by norm_num

theorem sub_nsw_value {a b : BitVec 64} (ha : a.toNat < 2 ^ 62) (hb : b.toNat < 2 ^ 62) :
    LLVM.sub (.value a) (.value b) { nsw := true } = .value (a - b) := by
  have hu : a.toInt = a.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hv : b.toInt = b.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hs : a.ssubOverflow b = false := by
    simp only [BitVec.ssubOverflow, hu, hv, pow63, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    omega
  simp [LLVM.sub, hs, LLVM.sub?]

theorem add_sub_nsw_value {a b c : BitVec 64} (ha : a.toNat < 2 ^ 62) (hb : b.toNat < 2 ^ 62)
    (hc : c.toNat < 2 ^ 62) :
    LLVM.add (.value (a - b)) (.value c) { nsw := true } = .value (a - b + c) := by
  have hu : a.toInt = a.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hv : b.toInt = b.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hw : c.toInt = c.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hab : (a - b).toInt = (a.toNat : ℤ) - b.toNat := by
    rw [BitVec.toInt_sub, hu, hv, Int.bmod]; split <;> omega
  have hs : (a - b).saddOverflow c = false := by
    simp only [BitVec.saddOverflow, hab, hw, pow63, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    omega
  simp [LLVM.add, hs, LLVM.add?]

/-- `%194`: a biased masked lane plus a carry, `nsw`. -/
theorem add_and_bias_sshr {x y m : BitVec 64} {c : ℕ} (fs : LLVM.NoWrapFlags)
    (hfs : fs.nuw = false) (hm : m.toNat < 2 ^ 44) (hc : c < 2 ^ 44) :
    LLVM.add (.value ((y &&& m) + BitVec.ofNat 64 c)) (.value (x.sshiftRight 43)) fs
      = .value ((y &&& m) + BitVec.ofNat 64 c + x.sshiftRight 43) := by
  have hb := sshr43_bounds x
  have hand : (y &&& m).toNat ≤ m.toNat := by simp only [BitVec.toNat_and]; exact Nat.and_le_right
  have hsum : ((y &&& m) + BitVec.ofNat 64 c).toNat < 2 ^ 45 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  have ht : ((y &&& m) + BitVec.ofNat 64 c).toInt = ((y &&& m) + BitVec.ofNat 64 c).toNat :=
    BitVec.toInt_eq_toNat_of_lt (by omega)
  have hs : ((y &&& m) + BitVec.ofNat 64 c).saddOverflow (x.sshiftRight 43) = false := by
    simp only [BitVec.saddOverflow, ht, pow63, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    omega
  simp [LLVM.add, hs, hfs, LLVM.add?]

/-! ## The runs -/

/-- `%69`/`%78`/`%87`: `p`'s limbs on the lanes `(E, H, G, F)` subtracts. -/
def pmaskEF (c d : BitVec 64) : Vector (LLVM.IntW 64) 8 :=
  #v[.value c, .poison, .poison, .value c, .value d, .poison, .poison, .value d]

/-- **`%110`/`%117`/`%118`/`%119`/`%126`/`%127`**: `(Y-X+c, X+Y, 2Z, T)`. -/
theorem denote_tb {x : Vector (BitVec 64) 8} {c d : BitVec 64}
    {z m a b e f g h : Vector (LLVM.IntW 64) 8} (hm : m = pmaskE c d)
    (ha : a = vshuf [1, 0, 2, 3, 5, 4, 6, 7] (x.map PoisonOr.value) z)
    (hb : b = vbin .sub a (x.map PoisonOr.value))
    (he : e = vbin .add b m)
    (hf : f = vshuf [0, 9, 10, 11, 4, 13, 14, 15] e a)
    (hg : g = vbin .add f (x.map PoisonOr.value))
    (hh : h = vshuf [0, 9, 10, 3, 4, 13, 14, 7] f g) :
    h = (tbVec c d x).map PoisonOr.value := by
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
  ge_lanes [tbVec, add_value]

/-- **`%163`/`%166`/`%167`/`%168`/`%175`/`%176`**: `(B-A+c, A+B, C+D, D-C+c)` over
`(A, B, D, C)`. -/
theorem denote_ehgf {v : Vector (BitVec 64) 8} {c d : BitVec 64} {fs : LLVM.NoWrapFlags}
    {z m a b e f g h : Vector (LLVM.IntW 64) 8} (hv : R43x6.U44 v)
    (hc : c.toNat < 2 ^ 62) (hd : d.toNat < 2 ^ 62) (hm : m = pmaskEF c d)
    (ha : a = vshuf [1, 0, 3, 2, 5, 4, 7, 6] (v.map PoisonOr.value) z)
    (hb : b = vbin (.sub { nsw := true }) a (v.map PoisonOr.value))
    (he : e = vbin (.add { nsw := true }) b m)
    (hf : f = vshuf [0, 9, 10, 3, 4, 13, 14, 7] e a)
    (hg : g = vbin (.add fs) f (v.map PoisonOr.value))
    (hh : h = vshuf [0, 9, 10, 3, 4, 13, 14, 7] f g) :
    h = (ehgfVec c d v).map PoisonOr.value := by
  have hl : ∀ (i : ℕ) (h : i < 8), (v[i]'h).toNat < 2 ^ 62 := fun i h => by
    have := unn_toNat v 44 (by omega) hv ⟨i, h⟩; simp only [Fin.getElem_fin] at this; omega
  subst hm
  replace ha : a = (#v[v[1], v[0], v[3], v[2], v[5], v[4], v[7], v[6]]
      : Vector (BitVec 64) 8).map PoisonOr.value := by subst ha; ge_lanes []
  subst ha
  replace hb : b = (#v[v[1] - v[0], v[0] - v[1], v[3] - v[2], v[2] - v[3], v[5] - v[4],
      v[4] - v[5], v[7] - v[6], v[6] - v[7]] : Vector (BitVec 64) 8).map PoisonOr.value := by
    subst hb
    apply Vector.ext; intro i hi
    interval_cases i <;> ge_lane_simp [] <;> exact sub_nsw_value (hl _ _) (hl _ _)
  subst hb
  replace hf : f = (#v[v[1] - v[0] + c, v[0], v[3], v[2] - v[3] + c, v[5] - v[4] + d, v[4], v[7],
      v[6] - v[7] + d] : Vector (BitVec 64) 8).map PoisonOr.value := by
    subst he hf
    apply Vector.ext; intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;> ge_lane_simp [pmaskEF] <;>
      first
      | rfl
      | exact add_sub_nsw_value (hl _ _) (hl _ _) hc
      | exact add_sub_nsw_value (hl _ _) (hl _ _) hd
  subst hf hg hh
  apply Vector.ext; intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i <;> ge_lane_simp [ehgfVec] <;>
    first
    | rfl
    | exact add_value_of_lt62 _ (hl _ _) (hl _ _)

/-- **The second `FD_R43X6_QUAD_FOLD_SIGNED`'s `03`**, `%181`, `%183`, `%186`-`%191`: the bias
goes on the carry. -/
theorem denote_foldSigned03' {P : Quad} {c60 c61 c63 c81 c82 c83 : Vector (LLVM.IntW 64) 8}
    (hc60 : c60 = toBitVecValue 64 nbias03) (hc61 : c61 = toBitVecValue 64 nbias)
    (hc63 : c63 = toBitVecValue 64 quadShift48) (hc81 : c81 = quadMul19)
    (hc82 : c82 = toBitVecValue 64 quadMask43) (hc83 : c83 = toBitVecValue 64 bias03)
    {a233 a235 a238 a239 a240 a241 a242 a243 : Vector (LLVM.IntW 64) 8}
    (h233 : a233 = vbin .add (P.v03.map PoisonOr.value) c60)
    (h235 : a235 = vbin .add (P.v25.map PoisonOr.value) c61)
    (h238 : a238 = vbin .ashr a235 c63)
    (h239 : a239 = vbin .mul a238 c81)
    (h240 : a240 = vbin .and a233 c82)
    (h241 : a241 = vshuf [4, 5, 6, 7, 8, 9, 10, 11] a239 a238)
    (h242 : a242 = vbin .add a241 c83)
    (h243 : a243 = vbin .add a242 a240) :
    a243 = (foldSignedQuad P).v03.map PoisonOr.value := by
  replace h233 := denote_nb03v hc60 h233
  replace h235 := denote_nbv hc61 h235
  subst hc63 hc81 hc82 hc83 h233 h235
  replace h238 : a238 = (#v[(nbv P.v25)[0].sshiftRight 43, (nbv P.v25)[1].sshiftRight 43,
      (nbv P.v25)[2].sshiftRight 43, (nbv P.v25)[3].sshiftRight 43,
      (nbv P.v25)[4].sshiftRight 40, (nbv P.v25)[5].sshiftRight 40,
      (nbv P.v25)[6].sshiftRight 40, (nbv P.v25)[7].sshiftRight 40]
      : Vector (BitVec 64) 8).map PoisonOr.value := by
    subst h238; ge_lanes [quadShift48, ashr_value]
  subst h238 h239 h240 h241 h242 h243
  apply Vector.ext; intro i hi
  interval_cases i <;>
    ge_lane_simp [quadMul19, mul_value, mul_poison, quadMask43, and_value, bias03, add_value,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, foldSignedQuad, fsL0, fsL3, nb03v, nbv] <;>
    ac_rfl

/-- **The second `FD_R43X6_QUAD_FOLD_SIGNED`'s `14`**, `%181`, `%182`, `%184`, `%192`-`%194`. -/
theorem denote_foldSigned14' {P : Quad} {c60 c61 c62 c82 c84 : Vector (LLVM.IntW 64) 8}
    (hc60 : c60 = toBitVecValue 64 nbias03) (hc61 : c61 = toBitVecValue 64 nbias)
    (hc62 : c62 = toBitVecValue 64 quadShift43) (hc82 : c82 = toBitVecValue 64 quadMask43)
    (hc84 : c84 = toBitVecValue 64 bias)
    {a233 a234 a236 a244 a245 a246 : Vector (LLVM.IntW 64) 8}
    (h233 : a233 = vbin .add (P.v03.map PoisonOr.value) c60)
    (h234 : a234 = vbin .add (P.v14.map PoisonOr.value) c61)
    (h236 : a236 = vbin .ashr a233 c62)
    (h244 : a244 = vbin .and a234 c82)
    (h245 : a245 = vbin (.add { nsw := true, nuw := true }) a244 c84)
    (h246 : a246 = vbin (.add { nsw := true }) a245 a236) :
    a246 = (foldSignedQuad P).v14.map PoisonOr.value := by
  replace h233 := denote_nb03v hc60 h233
  replace h234 := denote_nbv hc61 h234
  subst hc62 hc82 hc84 h233 h234 h236 h244 h245 h246
  apply Vector.ext; intro i hi
  interval_cases i <;>
    ge_lane_simp [quadShift43, ashr_value, quadMask43, and_value, bias, add_and_bias,
      add_and_bias_sshr, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, eq_self_iff_true,
      foldSignedQuad, fsMid, nb03v, nbv] <;>
    ac_rfl

theorem denote_permEGGE {v : Vector (BitVec 64) 8} {z a : Vector (LLVM.IntW 64) 8}
    (h : a = vshuf [0, 2, 2, 0, 4, 6, 6, 4] (v.map PoisonOr.value) z) :
    a = (permEGGE v).map PoisonOr.value := by
  subst h; ge_lanes [permEGGE]

theorem denote_permFHFH {v : Vector (BitVec 64) 8} {z a : Vector (LLVM.IntW 64) 8}
    (h : a = vshuf [3, 1, 3, 1, 7, 5, 7, 5] (v.map PoisonOr.value) z) :
    a = (permFHFH v).map PoisonOr.value := by
  subst h; ge_lanes [permFHFH]

end PointAdd

end Firedancer.Avx512

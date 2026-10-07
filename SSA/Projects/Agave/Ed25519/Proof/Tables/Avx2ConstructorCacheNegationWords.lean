import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorNormalizationWords

/-! Word-level obligations for the constructor's final D-coordinate negation.
The two bitcasts preserve the deliberately poisoned non-D lanes. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.CacheNegation
open LeanMLIR.RIR Avx2PointAdd CacheArithmetic
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] Ty.width

def sparse32 (lo hi : BitVec 32) : ⟦Ty.vec 8 32⟧ :=
  #v[.poison,.poison,.poison,.poison,.poison,.poison,.value lo,.value hi]

def sparse64 (x : BitVec 64) : ⟦Ty.vec 4 64⟧ :=
  #v[.poison,.poison,.poison,.value x]

theorem sparse_join (lo hi : BitVec 32) :
    Operation.bitcast (t := .vec 8 32) (t' := .vec 4 64) (by decide)
      (sparse32 lo hi) = sparse64 (hi ++ lo) := by
  apply Vector.ext
  intro i hi'
  interval_cases i
  · rfl
  · rfl
  · rfl
  · simpa [Operation.bitcast, sparse32, sparse64, Fin.exists_fin_succ] using
      congrArg PoisonOr.value (extract_pack_pair (#v[0,0,0,0,0,0,lo,hi] : V32) 3 (by decide))

theorem sparse_split (x : BitVec 64) :
    Operation.bitcast (t := .vec 4 64) (t' := .vec 8 32) (by decide)
      (sparse64 x) = sparse32 (x.extractLsb' 0 32) (x.extractLsb' 32 32) := by
  apply Vector.ext
  intro i hi
  interval_cases i
  all_goals try rfl
  · simpa [Operation.bitcast, sparse32, sparse64, Fin.exists_fin_succ] using
      congrArg PoisonOr.value (extract_pack_part (#v[0,0,0,x] : V64) 3 0 32 (by decide) (by decide))
  · simpa [Operation.bitcast, sparse32, sparse64, Fin.exists_fin_succ] using
      congrArg PoisonOr.value (extract_pack_part (#v[0,0,0,x] : V64) 3 32 32 (by decide) (by decide))

theorem sub_value (flagged : Bool) (x y : BitVec 32)
    (hx : x.toNat < 2^31) (hy : y.toNat ≤ x.toNat) :
    Operation.sub {nsw := flagged, nuw := flagged} (.value x) (.value y) =
      .value (x-y) := by
  have hxi : x.toInt = (x.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hyi : y.toInt = (y.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hs : x.ssubOverflow y = false := by
    simp only [BitVec.ssubOverflow, hxi, hyi, Bool.or_eq_false_iff,
      decide_eq_false_iff_not]
    constructor <;> norm_num at hx ⊢ <;> omega
  have hu : x.usubOverflow y = false := by
    simp [BitVec.usubOverflow, Nat.not_lt.mpr hy]
  simp [Operation.sub, hs, hu]

theorem sixteenP_small (i : Fin 10) : sixteenP i < 2^31 := by
  unfold sixteenP
  split_ifs <;> decide

theorem sub_word (flagged : Bool) {a : Avx2FieldMul.Limbs} (ha : reduced a)
    (i : Fin 10) :
    Operation.sub {nsw := flagged, nuw := flagged}
      (.value (word (sixteenP i))) (.value (word (a i))) =
      .value (word (negateColumns a i)) := by
  have hc := sixteenP_small i
  have ha' := reduced_le_sixteenP ha i
  have hcw : (word (sixteenP i)).toNat = sixteenP i := by
    exact Nat.mod_eq_of_lt (by omega)
  have haw : (word (a i)).toNat = a i := by
    exact Nat.mod_eq_of_lt (by omega)
  rw [sub_value flagged _ _ (by omega) (by omega)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega), hcw, haw]
  exact (Nat.mod_eq_of_lt (by have := Nat.sub_le (sixteenP i) (a i); omega)).symm

def top (x : BitVec 32) : BitVec 32 := (x >>> 25) &&& 15

theorem top_bound (x : BitVec 32) : (top x).toNat < 16 := by
  have h : ((x >>> 25).toNat &&& 15) ≤ 15 := Nat.and_le_right
  change ((x >>> 25).toNat &&& 15) < 16
  omega

theorem top_exact (x : BitVec 32) (hx : x.toNat < 2^29) :
    (top x).toNat = x.toNat / 2^25 := by
  simp only [top, BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  change (x.toNat / 2^25) &&& (2^4-1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (by norm_num at hx ⊢; omega)

theorem top_mul_low (x : BitVec 32) :
    ((top x).setWidth 64 * 19#64).extractLsb' 0 32 = top x * 19 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb', BitVec.toNat_mul, Avx2SquareNegateD.wide_toNat]

theorem top_mul_high (x : BitVec 32) :
    ((top x).setWidth 64 * 19#64).extractLsb' 32 32 = 0 := by
  have h := top_bound x
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb', BitVec.toNat_mul, Avx2SquareNegateD.wide_toNat,
    BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.shiftRight_eq_div_pow]
  have hp : (top x).toNat * 19 < 2^32 := by omega
  norm_num only [Nat.reducePow, Nat.reduceMod, Nat.shiftRight_zero]
  norm_num at hp
  rw [Nat.mod_eq_of_lt (lt_trans hp (by norm_num)), Nat.div_eq_of_lt hp]
  rfl

end Agave.Ed25519.Tables.Avx2Constructor.CacheNegation

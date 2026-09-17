/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_f25519_sub
import SSA.Projects.Firedancer.Avx512.Proof.Sub
import SSA.Projects.Firedancer.Avx512.Proof.Step.Basic
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Memory
import SSA.Projects.Firedancer.Proof.Tactics

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-! ## The operands' limbs -/

/-- The spec's `u47` hypothesis, as a bound on limbs. -/
theorem unreduced_limb_bounds {x : Vector (BitVec 64) 8}
    (h : R43x6.Unreduced (x.take R43x6.limbCount)) (k : Fin R43x6.limbCount) :
    0 ≤ R43x6.extractLimbs x k ∧ R43x6.extractLimbs x k < 2 ^ 47 := by
  have := R43x6.extractLimbs_bounds h k
  omega

/-! ## `Proof/Sub.lean`'s fold lemmas, at `2 ^ 48`

Same statements, same scripts, one window wider -- see the module docstring. -/

theorem acpBias_fitsLong48 {l : Fin R43x6.limbCount → ℤ}
    (hl : ∀ k, -(2 ^ 48) < l k ∧ l k < 2 ^ 48) (k : Fin R43x6.limbCount) :
    R43x6.FitsLong (acpLimb l k + biasLimb k) := by
  have h0 := hl 0; have h1 := hl 1; have h2 := hl 2
  have h3 := hl 3; have h4 := hl 4; have h5 := hl 5
  fin_cases k <;> simp only [Fin.zero_eta, acpLimb, biasLimb, R43x6.FitsLong] <;> omega

theorem extractLimbs_acpBiasVec48 {z : Vector (BitVec 64) 8}
    (hz : ∀ k, -(2 ^ 48) < R43x6.extractLimbs z k ∧ R43x6.extractLimbs z k < 2 ^ 48)
    (k : Fin R43x6.limbCount) :
    R43x6.extractLimbs (acpBiasVec z) k
      = acpLimb (R43x6.extractLimbs z) k + biasLimb k :=
  extractLimbs_limbVecInt _ (acpBias_fitsLong48 hz) k

/-- **The fold lands in `u44`** -- the `2 ^ 48` window costs three bits of
carry, and `u44` still has room for them. -/
theorem extractLimbs_acpBiasVec_bounds48 {z : Vector (BitVec 64) 8}
    (hz : ∀ k, -(2 ^ 48) < R43x6.extractLimbs z k ∧ R43x6.extractLimbs z k < 2 ^ 48)
    (k : Fin R43x6.limbCount) :
    0 ≤ R43x6.extractLimbs (acpBiasVec z) k
      ∧ R43x6.extractLimbs (acpBiasVec z) k < 2 ^ 44 := by
  have hw := extractLimbs_acpBiasVec48 hz k
  have h0 := hz 0; have h1 := hz 1; have h2 := hz 2
  have h3 := hz 3; have h4 := hz 4; have h5 := hz 5
  rw [hw]
  fin_cases k <;> simp only [Fin.zero_eta, acpLimb, biasLimb] <;> omega

theorem decode'_acpBiasVec48 {z : Vector (BitVec 64) 8}
    (hz : ∀ k, -(2 ^ 48) < R43x6.extractLimbs z k ∧ R43x6.extractLimbs z k < 2 ^ 48) :
    ((R43x6.decode' (acpBiasVec z) : ℤ) : ZMod p)
      = ((decodeNat (fun k => R43x6.extractLimbs z k + biasLimb k) : ℤ) : ZMod p) := by
  rw [acpBiasVec, decode'_limbVecInt _ (acpBias_fitsLong48 hz)]
  have hfold : (fun k => acpLimb (R43x6.extractLimbs z) k + biasLimb k)
      = foldSignedLimb (fun k => R43x6.extractLimbs z k + biasLimb k) := by
    funext k
    simp only [foldSignedLimb]
    congr 2
    funext j
    ring
  rw [hfold, decodeNat_foldSignedLimb_zmod]

/-! ## The vector the region stores

`private` only to stay out of `Proof/Field/fd_f25519_eq.lean`'s way: it has a
copy of this definition, and the two want to meet in `Proof/Sub.lean`. -/

/-- `fd_r43x6_fold_signed( fd_r43x6_sub_fast( x, y ) )`. -/
private def subFoldVec (x y : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  acpBiasVec (subFastVec x y)

private theorem subFast_fits48_1 {x y : Vector (BitVec 64) 8}
    (hx : R43x6.Unreduced (x.take R43x6.limbCount))
    (hy : R43x6.Unreduced (y.take R43x6.limbCount)) (k : Fin R43x6.limbCount) :
    R43x6.FitsLong (R43x6.extractLimbs x k - R43x6.extractLimbs y k) := by
  have h1 := unreduced_limb_bounds hx k
  have h2 := unreduced_limb_bounds hy k
  simp only [R43x6.FitsLong]
  omega

private theorem subFast_fits48_2 {x y : Vector (BitVec 64) 8}
    (hx : R43x6.Unreduced (x.take R43x6.limbCount))
    (hy : R43x6.Unreduced (y.take R43x6.limbCount)) (k : Fin R43x6.limbCount) :
    R43x6.FitsLong (R43x6.extractLimbs x k - R43x6.extractLimbs y k + subFastLimb k) := by
  have h1 := unreduced_limb_bounds hx k
  have h2 := unreduced_limb_bounds hy k
  have h3 := subFastLimb_bounds k
  simp only [R43x6.FitsLong]
  omega

/-- `sub_fast`'s limbs, on `u47` operands. -/
theorem extractLimbs_subFastVec_unreduced {x y : Vector (BitVec 64) 8}
    (hx : R43x6.Unreduced (x.take R43x6.limbCount))
    (hy : R43x6.Unreduced (y.take R43x6.limbCount)) (k : Fin R43x6.limbCount) :
    R43x6.extractLimbs (subFastVec x y) k
      = R43x6.extractLimbs x k - R43x6.extractLimbs y k + subFastLimb k :=
  extractLimbs_subFastVec (subFast_fits48_1 hx hy) (subFast_fits48_2 hx hy) k

/-- ... and their range: the fold's input window, which is why the `48` copies
above exist. -/
theorem subFastVec_unreduced_bounds {x y : Vector (BitVec 64) 8}
    (hx : R43x6.Unreduced (x.take R43x6.limbCount))
    (hy : R43x6.Unreduced (y.take R43x6.limbCount)) (k : Fin R43x6.limbCount) :
    -(2 ^ 48) < R43x6.extractLimbs (subFastVec x y) k
      ∧ R43x6.extractLimbs (subFastVec x y) k < 2 ^ 48 := by
  have h1 := unreduced_limb_bounds hx k
  have h2 := unreduced_limb_bounds hy k
  have h3 := subFastLimb_bounds k
  rw [extractLimbs_subFastVec_unreduced hx hy k]
  omega

/-- **The result is `u44`** -- the spec's first output class. -/
theorem subFoldVec_bounds {x y : Vector (BitVec 64) 8}
    (hx : R43x6.Unreduced (x.take R43x6.limbCount))
    (hy : R43x6.Unreduced (y.take R43x6.limbCount)) (k : Fin R43x6.limbCount) :
    0 ≤ R43x6.extractLimbs (subFoldVec x y) k
      ∧ R43x6.extractLimbs (subFoldVec x y) k < 2 ^ 44 :=
  extractLimbs_acpBiasVec_bounds48 (subFastVec_unreduced_bounds hx hy) k

/-- The two lanes the fold zeroes: `limbVecInt` puts `0` there by construction. -/
theorem subFoldVec_six (x y : Vector (BitVec 64) 8) : (subFoldVec x y)[6] = 0 := rfl
theorem subFoldVec_seven (x y : Vector (BitVec 64) 8) : (subFoldVec x y)[7] = 0 := rfl

/-- **The element it holds**: `a - b`, `sub_fast`'s `p` and the fold's bias
both having cancelled. -/
theorem vecValue_subFoldVec {x y : Vector (BitVec 64) 8}
    (hx : R43x6.Unreduced (x.take R43x6.limbCount))
    (hy : R43x6.Unreduced (y.take R43x6.limbCount)) :
    vecValue (subFoldVec x y) = vecValue x - vecValue y := by
  -- the limbs the fold saw, decoded: `a - b + p`
  have hsplit : (fun k => R43x6.extractLimbs (subFastVec x y) k + biasLimb k)
      = (fun k => (R43x6.extractLimbs x k - R43x6.extractLimbs y k)
          + (subFastLimb k + biasLimb k)) := by
    funext k
    rw [extractLimbs_subFastVec_unreduced hx hy k]
    ring
  have hz : decodeNat (fun k => R43x6.extractLimbs (subFastVec x y) k + biasLimb k)
      = R43x6.decode' x - R43x6.decode' y + (p : ℤ) := by
    rw [hsplit, decodeNat_add, decodeNat_sub, decodeNat_subFastLimb]
    show R43x6.decodeLimbs (R43x6.extractLimbs x) - R43x6.decodeLimbs (R43x6.extractLimbs y)
      + (p : ℤ) = _
    rw [R43x6.decodeLimbs_extractLimbs, R43x6.decodeLimbs_extractLimbs]
  have hcastx : ((R43x6.decode' x : ℤ) : ZMod p) = vecValue x :=
    decode'_cast_eq_vecValue62 x fun k => by have := unreduced_limb_bounds hx k; omega
  have hcasty : ((R43x6.decode' y : ℤ) : ZMod p) = vecValue y :=
    decode'_cast_eq_vecValue62 y fun k => by have := unreduced_limb_bounds hy k; omega
  have hcast : ((R43x6.decode' (subFoldVec x y) : ℤ) : ZMod p) = vecValue (subFoldVec x y) :=
    decode'_cast_eq_vecValue62 _ fun k => by have := subFoldVec_bounds hx hy k; omega
  rw [← hcast]
  show ((R43x6.decode' (acpBiasVec (subFastVec x y)) : ℤ) : ZMod p) = _
  rw [decode'_acpBiasVec48 (subFastVec_unreduced_bounds hx hy), hz, ← hcastx, ← hcasty]
  push_cast
  simp

/-! ## The fold, as *this* region emits it

`denote_acpBiasVec` with the bias moved off the tail and onto the carry
vector: `%17 = _c + b`, `%18 = %17 + _xl`, `%19 = %18 + _d`. Every add is
plain (`overflow<none>`), so this is `denote_acpBiasVec`'s script with the
three summands reassociated -- the closing `ring` should absorb the
difference. -/
/-- `Fold.lean`'s constant-shuffling helpers, which are `private` there. -/
private theorem and_ones64 (x : BitVec 64) : x &&& 18446744073709551615#64 = x := by
  bv_decide

private theorem fin6_one : ((1 : Fin 6) : ℕ) = 1 := rfl
private theorem fin6_two : ((2 : Fin 6) : ℕ) = 2 := rfl
private theorem fin6_three : ((3 : Fin 6) : ℕ) = 3 := rfl
private theorem fin6_four : ((4 : Fin 6) : ℕ) = 4 := rfl
private theorem fin6_five : ((5 : Fin 6) : ℕ) = 5 := rfl

private theorem ofNat18 : (18#64 : BitVec 64) = BitVec.ofInt 64 18 := rfl
private theorem ofNatBias0 : (159383552#64 : BitVec 64) = BitVec.ofInt 64 (19 * 2 ^ 23) := rfl
private theorem ofNatBias : (1048576#64 : BitVec 64) = BitVec.ofInt 64 (2 ^ 20) := rfl

theorem denote_subFoldVec {z : Vector (BitVec 64) 8}
    {a12 a13 a14 a15 a16 a17 a18 a19 : Vector (LLVM.IntW 64) 8}
    (h12 : a12 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .and
      (z.map PoisonOr.value)[i.val]
      (toBitVecValue 64 #v[8796093022207, 8796093022207, 8796093022207, 8796093022207,
        8796093022207, 1099511627775, 0, 0])[i.val])
    (h13 : a13 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .ashr
      (z.map PoisonOr.value)[i.val] (toBitVecValue 64 #v[43, 43, 43, 43, 43, 40, 0, 0])[i.val])
    (h14 : a14 = LLVM.Ty.vpermi2var a13 (toBitVecValue 64 #v[5, 0, 1, 2, 3, 4, 8, 8])
      (toBitVecValue 64 #v[0, 0, 0, 0, 0, 0, 0, 0]))
    (h15 : a15 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .mul
      a14[i.val] (toBitVecValue 64 #v[18, 18, 18, 18, 18, 18, 18, 18])[i.val])
    (h16 : a16 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .and
      a15[i.val] (toBitVecValue 64 #v[18446744073709551615, 0, 0, 0, 0, 0, 0, 0])[i.val])
    (h17 : a17 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .add a14[i.val]
      (toBitVecValue 64 #v[159383552, 1048576, 1048576, 1048576, 1048576, 1048576, 0, 0])[i.val])
    (h18 : a18 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .add a17[i.val] a12[i.val])
    (h19 : a19 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .add a18[i.val] a16[i.val]) :
    a19 = (acpBiasVec z).map PoisonOr.value := by
  rw [denote_vec_and_const] at h12
  rw [denote_vec_ashr_const _ _ (by decide)] at h13
  rw [h13, denote_vec_rotate] at h14
  subst h12 h14 h15 h16 h17 h18 h19
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp only [Vector.getElem_ofFn, Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, InstCombine.binaryDenote,
      LLVM.mul, LLVM.and, LLVM.add, toBitVecValue, PoisonOr.value_bind,
      LLVM.mul?, LLVM.and?, LLVM.add?, Bool.false_eq_true, false_and, if_false,
      acpBiasVec, limbVecInt, acpLimb, biasLimb, R43x6.extractLimbs,
      LimbRepresentations.toInts, and_mask43_int, and_mask40_int, sshiftRight_ofInt,
      and_ones64, BitVec.and_zero, ofNat18, ofNatBias0, ofNatBias,
      BitVec.add_zero, Fin.isValue, Fin.val_zero,
      fin6_one, fin6_two, fin6_three, fin6_four, fin6_five,
      ← BitVec.ofInt_mul, ← BitVec.ofInt_add, R43x6.shiftRight_eq, Fin.val_castLE] <;>
    congr 2 <;>
    ring

/-- `Step/Basic.lean`'s `unflatten_readVec` with the width already a literal,
which is how `peel_load` leaves it. -/
private theorem unflatten_readVec_512 {m : MemoryState} {p : Pointer} (h : IsVecPtr m p)
    {blk : LiveBlock} (hblk : m.live? p.id = some blk) :
    LLVM.Ty.unflatten (.vector 8 (.bitvec (.concrete 64)))
        (blk.bytes.extractLsb' p.offsetInBits 512)
      = (readVec h).map PoisonOr.value :=
  unflatten_readVec h hblk

/-! ## The walk -/

/-- The `u44` of `subFoldVec_bounds`, in the `R43x6.UNN` form the spec states
its output class in. -/
theorem subFoldVec_u44 {x y : Vector (BitVec 64) 8}
    (hx : R43x6.Unreduced (x.take R43x6.limbCount))
    (hy : R43x6.Unreduced (y.take R43x6.limbCount)) :
    R43x6.U44 ((subFoldVec x y).take R43x6.limbCount) := by
  refine ⟨fun i => ?_, fun i => ?_⟩ <;>
  · rw [R43x6.toInts_take]
    have := subFoldVec_bounds hx hy i
    omega

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
theorem fd_f25519_sub_conforms (r a b : Pointer) (s : GlobalState) (hs : s.WF)
    (hr : IsVecPtr s.mem r) (ha : IsVecPtr s.mem a) (hb : IsVecPtr s.mem b) :
    fd_f25519_sub_spec r a b s hr ha hb := by
  simp only [fd_f25519_sub_spec, fd_f25519_sub, Cfg.denote]
  intro haU hbU
  refine Firedancer.run_runFunction' _ ?_

  obtain ⟨blkA, hblkA, hlenA⟩ := ha.1
  obtain ⟨blkB, hblkB, hlenB⟩ := hb.1
  have hliveA : s.mem.live? a.id = some blkA := by simp only [MemoryState.live?, hblkA]
  have hliveB : s.mem.live? b.id = some blkB := by simp only [MemoryState.live?, hblkB]
  denote_step_all v 7
  -- The constants stay as hypotheses in `toBitVecValue` form: `eval_consts`
  -- would substitute them away as `LLVM.Ty.dense …`, which is built from
  -- `Vector.ofFn`/`BitVec.ofInt` where every denote lemma of
  -- `Fold.lean`/`Sub.lean` matches `Vector.map`/`BitVec.ofNat`, and the two
  -- are not defeq.
  replace hv0 : v0 = toBitVecValue 64 #v[8795933638637, 8796091973631, 8796091973631,
    8796091973631, 8796091973631, 1099510579199, 0, 0] := by denote_dense hv0
  replace hv1 : v1 = toBitVecValue 64 #v[8796093022207, 8796093022207, 8796093022207,
    8796093022207, 8796093022207, 1099511627775, 0, 0] := by denote_dense hv1
  replace hv2 : v2 = toBitVecValue 64 #v[43, 43, 43, 43, 43, 40, 0, 0] := by denote_dense hv2
  replace hv3 : v3 = toBitVecValue 64 #v[5, 0, 1, 2, 3, 4, 8, 8] := by denote_dense hv3
  replace hv4 : v4 = toBitVecValue 64 #v[0, 0, 0, 0, 0, 0, 0, 0] := by denote_dense hv4
  replace hv5 : v5 = toBitVecValue 64 #v[18, 18, 18, 18, 18, 18, 18, 18] := by denote_dense hv5
  replace hv6 : v6 = toBitVecValue 64 #v[18446744073709551615, 0, 0, 0, 0, 0, 0, 0] := by
    denote_dense hv6
  replace hv7 : v7 = toBitVecValue 64 #v[159383552, 1048576, 1048576, 1048576, 1048576,
    1048576, 0, 0] := by denote_dense hv7
  peel_load (.vector 8 (.bitvec (.concrete 64))), blkA, a, hblkA, s
  rw [unflatten_readVec_512 ha hliveA]
  peel_load (.vector 8 (.bitvec (.concrete 64))), blkB, b, hblkB, s
  rw [unflatten_readVec_512 hb hliveB]
  denote_step_reduce v 19 only [hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, LLVM.sub, LLVM.sub?, LLVM.add, LLVM.add?]
  replace hv11 : v11 = (subFastVec (readVec ha) (readVec hb)).map PoisonOr.value := by
    rw [hv11, hv10]
    apply Vector.ext
    intro i hi
    simp [toBitVecValue, InstCombine.binaryDenote, LLVM.add, LLVM.add?, LLVM.sub, LLVM.sub?, subFastVec, subFastConst]
    interval_cases i <;> simp
  -- ... then the eight of `fd_r43x6_fold_signed`, in this region's shape.
  simp only [hv11] at hv12 hv13
  replace hv19 : v19 = (subFoldVec (readVec ha) (readVec hb)).map PoisonOr.value :=
    denote_subFoldVec hv12 hv13 hv14 hv15 hv16 hv17 hv18 hv19
  rw [hv19]
  peel_store subFoldVec (readVec ha) (readVec hb), r, hr.left, s
  simp_return

  have hkill : (s.popFrame
        (s.mem.splice r (vecBV (subFoldVec (readVec ha) (readVec hb)))) : GlobalState)
        ≈ { s with mem := s.mem.splice r (vecBV (subFoldVec (readVec ha) (readVec hb))) } :=
      killFrom_equiv_of_none fun q hq => live?_splice_eq_none (hs q hq)

  refine ⟨subFoldVec (readVec ha) (readVec hb), hkill, ?_⟩

  have hread : readVec (isVecPtr_of_equiv (GlobalState.Equiv.symm hkill) (isVecPtr_splice hr))
      = subFoldVec (readVec ha) (readVec hb) := by
    refine readVec_eq_of ?_
    rw [readVec?_of_live?_eq (hkill.live r.id)]
    exact readVec?_splice_self _ hr
  rw [hread]
  exact ⟨vecValue_subFoldVec haU hbU, subFoldVec_u44 haU hbU,
    subFoldVec_six _ _, subFoldVec_seven _ _⟩

end Firedancer.Avx512

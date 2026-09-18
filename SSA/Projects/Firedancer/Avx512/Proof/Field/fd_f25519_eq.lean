/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_f25519_eq
import SSA.Projects.Firedancer.Avx512.Proof.Sub
import SSA.Projects.Firedancer.Avx512.Proof.Step.Basic
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Memory
import SSA.Projects.Firedancer.Proof.Tactics

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-! ## The two patterns `fd_f25519_is_zero` tests, and the difference it reads -/

/-- What `fd_f25519_sub` leaves at its destination:
`fd_r43x6_fold_signed( fd_r43x6_sub_fast( x, y ) )`. -/
def subFoldVec (x y : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  acpBiasVec (subFastVec x y)

/-! ## What `R43x6.Reduced` buys -/

/-- A reduced vector's limbs, in the one-sided form the arithmetic takes. -/
theorem reduced_limb_bounds {x : Vector (BitVec 64) 8} (h : R43x6.Reduced x)
    (k : Fin R43x6.limbCount) :
    0 ≤ R43x6.extractLimbs x k ∧ R43x6.extractLimbs x k < 2 ^ 43 := by
  rcases Nat.lt_or_ge (k : ℕ) 5 with hk | hk
  · exact h.1 k hk
  · have hk5 : k = (5 : Fin R43x6.limbCount) := by
      refine Fin.eq_of_val_eq ?_
      have hlt := k.isLt
      show (k : ℕ) = 5
      simp only [R43x6.limbCount] at hlt
      omega
    rw [hk5]
    exact ⟨h.2.1.1, by have := h.2.1.2; omega⟩

/-- The value of a reduced vector, as an integer in `[0, p)`. -/
theorem reduced_decode'_bounds {x : Vector (BitVec 64) 8} (h : R43x6.Reduced x) :
    0 ≤ R43x6.decode' x ∧ R43x6.decode' x < (p : ℤ) := by
  refine ⟨?_, h.2.2⟩
  have h0 := reduced_limb_bounds h 0
  have h1 := reduced_limb_bounds h 1
  have h2 := reduced_limb_bounds h 2
  have h3 := reduced_limb_bounds h 3
  have h4 := reduced_limb_bounds h 4
  have h5 := reduced_limb_bounds h 5
  rw [← R43x6.decodeLimbs_extractLimbs, R43x6.decodeLimbs_eq]
  omega

/-- `decode'` and `vecValue` agree on a reduced vector: its limbs are well
inside the `[0, 2^44)` band `decode'_cast_eq_vecValue` asks for. -/
theorem decode'_cast_reduced {x : Vector (BitVec 64) 8} (h : R43x6.Reduced x) :
    ((R43x6.decode' x : ℤ) : ZMod p) = vecValue x :=
  decode'_cast_eq_vecValue x fun k => by
    have := reduced_limb_bounds h k; omega

/-- Every limb, the top one included, in `[0, 2^43)`: what `sub_fast` and digit uniqueness need. -/
abbrev Limbs43 (x : Vector (BitVec 64) 8) : Prop :=
  ∀ k : Fin R43x6.limbCount, 0 ≤ R43x6.extractLimbs x k ∧ R43x6.extractLimbs x k < 2 ^ 43

/-- **Close representations are unique.** Two vectors of `[0, 2^43)` limbs holding the same element,
whose values differ by less than `p`, agree limb for limb -- the fact that makes the `a = b` branch
a statement about bit patterns. -/
theorem extractLimbs_eq_of_value_eq' {x y : Vector (BitVec 64) 8}
    (hx : Limbs43 x) (hy : Limbs43 y) (hxy : R43x6.decode' x < R43x6.decode' y + p)
    (hyx : R43x6.decode' y < R43x6.decode' x + p) (h : vecValue x = vecValue y)
    (k : Fin R43x6.limbCount) : R43x6.extractLimbs x k = R43x6.extractLimbs y k := by
  have hcast : ((R43x6.decode' x : ℤ) : ZMod p) = ((R43x6.decode' y : ℤ) : ZMod p) := by
    rw [decode'_cast_eq_vecValue x fun k => by have := hx k; omega,
      decode'_cast_eq_vecValue y fun k => by have := hy k; omega, h]
  have hdec : R43x6.decode' x = R43x6.decode' y := by
    obtain ⟨c, hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hcast
    have hc0 : c = 0 := by
      rcases lt_trichotomy c 0 with hc' | hc' | hc'
      · nlinarith
      · exact hc'
      · nlinarith
    rw [hc0, mul_zero] at hc
    omega
  -- ... so the limbs, each inside its own digit, agree
  rw [← R43x6.decodeLimbs_extractLimbs, ← R43x6.decodeLimbs_extractLimbs,
    R43x6.decodeLimbs_eq, R43x6.decodeLimbs_eq] at hdec
  have hx0 := hx 0
  have hx1 := hx 1
  have hx2 := hx 2
  have hx3 := hx 3
  have hx4 := hx 4
  have hx5 := hx 5
  have hy0 := hy 0
  have hy1 := hy 1
  have hy2 := hy 2
  have hy3 := hy 3
  have hy4 := hy 4
  have hy5 := hy 5
  have e0 : R43x6.extractLimbs x 0 = R43x6.extractLimbs y 0 := by omega
  have e1 : R43x6.extractLimbs x 1 = R43x6.extractLimbs y 1 := by omega
  have e2 : R43x6.extractLimbs x 2 = R43x6.extractLimbs y 2 := by omega
  have e3 : R43x6.extractLimbs x 3 = R43x6.extractLimbs y 3 := by omega
  have e4 : R43x6.extractLimbs x 4 = R43x6.extractLimbs y 4 := by omega
  have e5 : R43x6.extractLimbs x 5 = R43x6.extractLimbs y 5 := by omega
  fin_cases k <;> first | exact e0 | exact e1 | exact e2 | exact e3 | exact e4 | exact e5

/-- **A reduced representation is unique.** -/
theorem extractLimbs_eq_of_value_eq {x y : Vector (BitVec 64) 8}
    (hx : R43x6.Reduced x) (hy : R43x6.Reduced y) (h : vecValue x = vecValue y)
    (k : Fin R43x6.limbCount) : R43x6.extractLimbs x k = R43x6.extractLimbs y k :=
  have hbx := reduced_decode'_bounds hx
  have hby := reduced_decode'_bounds hy
  extractLimbs_eq_of_value_eq' (reduced_limb_bounds hx) (reduced_limb_bounds hy) (by omega)
    (by omega) h k

/-! ## The difference `fd_f25519_sub` leaves

`sub_fast` is exact and its constant carries the fold's bias, so the vector
`fd_f25519_is_zero` reads is `acpBiasVec (subFastVec a b)`. Reduced inputs put
every intermediate far inside a `long`, which is what the limb lemmas of
`Proof/Sub.lean` ask for. -/

private theorem subFast_fits1 {x y : Vector (BitVec 64) 8}
    (hx : Limbs43 x) (hy : Limbs43 y) (k : Fin R43x6.limbCount) :
    R43x6.FitsLong (R43x6.extractLimbs x k - R43x6.extractLimbs y k) := by
  have h1 := hx k
  have h2 := hy k
  simp only [R43x6.FitsLong]
  omega

private theorem subFast_fits2 {x y : Vector (BitVec 64) 8}
    (hx : Limbs43 x) (hy : Limbs43 y) (k : Fin R43x6.limbCount) :
    R43x6.FitsLong (R43x6.extractLimbs x k - R43x6.extractLimbs y k + subFastLimb k) := by
  have h1 := hx k
  have h2 := hy k
  have h3 := subFastLimb_bounds k
  simp only [R43x6.FitsLong]
  omega

/-- `sub_fast`'s limbs, on reduced operands. -/
theorem extractLimbs_subFastVec_reduced {x y : Vector (BitVec 64) 8}
    (hx : Limbs43 x) (hy : Limbs43 y) (k : Fin R43x6.limbCount) :
    R43x6.extractLimbs (subFastVec x y) k
      = R43x6.extractLimbs x k - R43x6.extractLimbs y k + subFastLimb k :=
  extractLimbs_subFastVec (subFast_fits1 hx hy) (subFast_fits2 hx hy) k

/-- ... and their range, the input contract of the fold. -/
theorem subFastVec_reduced_bounds {x y : Vector (BitVec 64) 8}
    (hx : Limbs43 x) (hy : Limbs43 y) (k : Fin R43x6.limbCount) :
    -(2 ^ 45) < R43x6.extractLimbs (subFastVec x y) k
      ∧ R43x6.extractLimbs (subFastVec x y) k < 2 ^ 45 := by
  have h1 := hx k
  have h2 := hy k
  have h3 := subFastLimb_bounds k
  rw [extractLimbs_subFastVec_reduced hx hy k]
  omega

/-- The limbs the fold hands back are `u44`, which is what reads the result as
a `ℕ`-limbed vector again. -/
theorem subFoldVec_bounds_reduced {x y : Vector (BitVec 64) 8}
    (hx : Limbs43 x) (hy : Limbs43 y) (k : Fin R43x6.limbCount) :
    0 ≤ R43x6.extractLimbs (subFoldVec x y) k
      ∧ R43x6.extractLimbs (subFoldVec x y) k < 2 ^ 44 :=
  extractLimbs_acpBiasVec_bounds (subFastVec_reduced_bounds hx hy) k

/-- **The element the difference holds**: `a - b`, the bias and the `p` of
`sub_fast` both having cancelled. -/
theorem vecValue_subFoldVec_reduced {x y : Vector (BitVec 64) 8}
    (hx : Limbs43 x) (hy : Limbs43 y) :
    vecValue (subFoldVec x y) = vecValue x - vecValue y := by
  -- the limbs the fold saw, decoded: `a - b + p`
  have hsplit : (fun k => R43x6.extractLimbs (subFastVec x y) k + biasLimb k)
      = (fun k => (R43x6.extractLimbs x k - R43x6.extractLimbs y k)
          + (subFastLimb k + biasLimb k)) := by
    funext k
    rw [extractLimbs_subFastVec_reduced hx hy k]
    ring
  have hz : decodeNat (fun k => R43x6.extractLimbs (subFastVec x y) k + biasLimb k)
      = R43x6.decode' x - R43x6.decode' y + (p : ℤ) := by
    rw [hsplit, decodeNat_add, decodeNat_sub, decodeNat_subFastLimb]
    show R43x6.decodeLimbs (R43x6.extractLimbs x) - R43x6.decodeLimbs (R43x6.extractLimbs y)
      + (p : ℤ) = _
    rw [R43x6.decodeLimbs_extractLimbs, R43x6.decodeLimbs_extractLimbs]
  have hcast : ((R43x6.decode' (subFoldVec x y) : ℤ) : ZMod p) = vecValue (subFoldVec x y) :=
    decode'_cast_eq_vecValue _ fun k => by have := subFoldVec_bounds_reduced hx hy k; omega
  rw [← hcast]
  show ((R43x6.decode' (acpBiasVec (subFastVec x y)) : ℤ) : ZMod p) = _
  rw [decode'_acpBiasVec (subFastVec_reduced_bounds hx hy), hz,
    ← decode'_cast_eq_vecValue x fun k => by have := hx k; omega,
    ← decode'_cast_eq_vecValue y fun k => by have := hy k; omega]
  push_cast
  simp

/-! ## The two patterns, as elements -/

theorem vecValue_zeroVec : vecValue zeroVec = 0 := by
  rw [vecValue_eq_decodeNat]
  have h : decodeNat (limbNat zeroVec) = 0 := by decide
  rw [h, Nat.cast_zero]

theorem vecValue_pVec : vecValue pVec = 0 := by
  rw [vecValue_eq_decodeNat]
  have h : decodeNat (limbNat pVec) = p := by decide
  rw [h, ZMod.natCast_self]

/-- **When the difference is `fd_r43x6_p()`.** Equal reduced operands make
every `sub_fast` limb the constant's own -- `p`'s, with the bias taken out --
and each is inside its mask, so the carry propagate is the identity and the
bias goes straight back on. -/
theorem subFoldVec_of_extractLimbs_eq {x y : Vector (BitVec 64) 8}
    (hx : Limbs43 x) (hy : Limbs43 y)
    (h : ∀ k, R43x6.extractLimbs x k = R43x6.extractLimbs y k) :
    subFoldVec x y = pVec := by
  have harg : R43x6.extractLimbs (subFastVec x y) = subFastLimb := by
    funext k
    rw [extractLimbs_subFastVec_reduced hx hy k, h k]
    ring
  show acpBiasVec (subFastVec x y) = pVec
  rw [acpBiasVec, harg]
  decide


/-! ## `fd_f25519_is_zero`, as the region computes it

An exact bit-pattern test: two `wwl_eq`s, one against `fd_r43x6_zero()` and one
against `fd_r43x6_p()`, each a lane-wise `ne` compare whose `<8 x i1>` mask is
bitcast to an `i8` and tested against zero. -/

/-- The `i8` a `wwl_eq( x, c )` leaves: bit `i` says lane `i` differs. -/
def neMask (x c : Vector (BitVec 64) 8) : BitVec 8 :=
  BitVec.packLanes (Vector.ofFn fun i : Fin 8 => BitVec.ofBool (x[i.val] != c[i.val]))

/-- **What the compare and the bitcast leave.** Both operands are defined, so
no lane of the mask is poison and the `bitcast` is the flat round trip. -/
theorem bitcast_vicmp_ne_neMask (x c : Vector (BitVec 64) 8) :
    SLLVM.bitcast (.vector 8 (.bitvec (.concrete 1))) (.bitvec (.concrete 8))
        (SLLVM.vicmp LLVM.IntPred.ne (x.map PoisonOr.value) (c.map PoisonOr.value))
      = PoisonOr.value (neMask x c) := by
  simp only [SLLVM.bitcast, SLLVM.vicmp, LLVM.Ty.flattenBV, LLVM.Ty.poisonMask,
    LLVM.Ty.unflattenMasked, LLVM.Ty.width, LLVM.icmp, LLVM.icmp?, neMask]
  simp [LLVM.icmp', LLVM.Ty.width, BitVec.packLanes_eq_zero]

/-- ... and the `icmp eq …, 0` that reads it decides the whole vector. -/
theorem neMask_eq_zero_iff (x c : Vector (BitVec 64) 8) : neMask x c = 0 ↔ x = c := by
  constructor
  · intro h
    apply Vector.ext
    intro i hi
    have hlane := BitVec.extractLsb'_packLanes
      (Vector.ofFn fun j : Fin 8 => BitVec.ofBool (x[j.val] != c[j.val])) i hi
    rw [show (BitVec.packLanes (Vector.ofFn fun j : Fin 8 =>
      BitVec.ofBool (x[j.val] != c[j.val]))) = neMask x c from rfl, h] at hlane
    simp only [Vector.getElem_ofFn] at hlane
    have hb : (x[i] != c[i]) = false := by
      have h0 := hlane.symm
      revert h0
      cases h' : (x[i] != c[i]) <;> simp
    simpa using hb
  · intro h
    subst h
    exact BitVec.packLanes_eq_zero _ (by intro i hi; simp)


/-- `Step/Basic.lean`'s `unflatten_readVec` with the width already a literal,
which is how `peel_load` leaves it. -/
private theorem unflatten_readVec_512 {m : MemoryState} {p : Pointer} (h : IsVecPtr m p)
    {blk : LiveBlock} (hblk : m.live? p.id = some blk) :
    LLVM.Ty.unflatten (.vector 8 (.bitvec (.concrete 64)))
        (blk.bytes.extractLsb' p.offsetInBits 512)
      = (readVec h).map PoisonOr.value :=
  unflatten_readVec h hblk

/-- **What `fd_f25519_is_zero` returns**, with no hypothesis on what it reads:
`1` exactly at the two bit patterns it tests for. -/
theorem isZero_pattern (q : Pointer) (s : GlobalState) (hs : s.WF) (hq : IsVecPtr s.mem q) :
    ∃ s' : GlobalState,
      StateT.run (runFunction (fd_f25519_is_zero.denote
          (Ctxt.Valuation.singleton (.value q)))) s
        = .value ([(.value (if readVec hq = zeroVec ∨ readVec hq = pVec then 1#32 else 0#32)
            : LLVM.IntW 32)]ₕ, s') ∧ s ≈ s' := by
  simp only [fd_f25519_is_zero, Cfg.denote]
  refine Firedancer.run_runFunction' _ ?_
  refine ⟨s, ?_, hs.popFrame_equiv⟩
  obtain ⟨blk, hblk, hlen⟩ := hq.1
  have hlive : s.mem.live? q.id = some blk := by simp only [MemoryState.live?, hblk]
  denote_step_all v 3
  eval_consts v 0 3
  peel_load (.vector 8 (.bitvec (.concrete 64))), blk, q, hblk, s
  rw [unflatten_readVec_512 hq hlive]
  denote_step_all v 12
  denote_eval v 5 12
  -- the two constants the region compares against
  have hzero : LLVM.Ty.dense (InstCombine.MTy.vector 8 (InstCombine.MTy.bitvec (.concrete 64))) [0]
      = zeroVec.map PoisonOr.value := by
    apply Vector.ext (n := 8)
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.dense, zeroVec]
  have hpv : LLVM.Ty.dense (InstCombine.MTy.vector 8 (InstCombine.MTy.bitvec (.concrete 64)))
      [8796093022189, 8796093022207, 8796093022207, 8796093022207, 8796093022207,
        1099511627775, 0, 0] = pVec.map PoisonOr.value := by
    apply Vector.ext (n := 8)
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.dense, pVec]
  rw [hzero] at hv5
  rw [hpv] at hv8
  rw [hv5, bitcast_vicmp_ne_neMask] at hv6
  rw [hv8, bitcast_vicmp_ne_neMask] at hv9
  eval_llvm 7
  eval_llvm 10
  eval_llvm 11
  eval_llvm 12
  -- the `select` is the disjunction of the two pattern tests
  have hval : v12 = PoisonOr.value
      (if readVec hq = zeroVec ∨ readVec hq = pVec then 1#32 else 0#32) := by
    have hself : ∀ x : Vector (BitVec 64) 8, (neMask x x == 0#8) = true := fun x => by
      simp [(neMask_eq_zero_iff x x).mpr rfl]
    have hne : ∀ {x c : Vector (BitVec 64) 8}, x ≠ c → (neMask x c == 0#8) = false := by
      intro x c h
      simpa using fun hc => h ((neMask_eq_zero_iff x c).mp hc)
    rw [hv12]
    by_cases h0 : readVec hq = zeroVec
    · rw [h0, hself]
      simp
    · by_cases h1 : readVec hq = pVec
      · rw [h1, hne (show pVec ≠ zeroVec by decide), hself]
        simp
      · rw [hne h0, hne h1]
        simp [h0, h1]
  rw [hval]
  simp_return


/-! ## `fd_f25519_sub`, as the region computes it

Twelve instructions: two loads, the `sub_fast` pair, `fd_r43x6_fold_signed`,
a whole-vector store and the destination back. No flag on any of them is
`nsw`/`nuw`, so the vector it leaves is `acpBiasVec (subFastVec a b)` with no
hypothesis on what it read.

`Proof/Fold.lean` carries the fold in two shapes already; this region emits a
third -- the bias goes onto the *rotated carries* rather than onto the masked
lanes, and its `add` is unflagged -- so the eight instructions get their own
`denote_*`, proved the same way. -/

/-! `Proof/Fold.lean` keeps these five `private`; the lane script below needs
them in exactly the same places. -/

private theorem fin6_one : ((1 : Fin 6) : ℕ) = 1 := rfl
private theorem fin6_two : ((2 : Fin 6) : ℕ) = 2 := rfl
private theorem fin6_three : ((3 : Fin 6) : ℕ) = 3 := rfl
private theorem fin6_four : ((4 : Fin 6) : ℕ) = 4 := rfl
private theorem fin6_five : ((5 : Fin 6) : ℕ) = 5 := rfl
private theorem ofNat18 : (18#64 : BitVec 64) = BitVec.ofInt 64 18 := rfl
private theorem ofNatBias0 : (159383552#64 : BitVec 64) = BitVec.ofInt 64 (19 * 2 ^ 23) := rfl
private theorem ofNatBias : (1048576#64 : BitVec 64) = BitVec.ofInt 64 (2 ^ 20) := rfl

set_option maxHeartbeats 1000000 in
/-- **`fd_r43x6_fold_signed`, as `fd_f25519_sub` emits it.** -/
theorem denote_acpBiasVec_permBias {z : Vector (BitVec 64) 8}
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
      (toBitVecValue 64
        #v[159383552, 1048576, 1048576, 1048576, 1048576, 1048576, 0, 0])[i.val])
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
      and_allOnes_64, BitVec.and_zero, ofNat18, ofNatBias0, ofNatBias,
      BitVec.add_zero, Fin.isValue, Fin.val_zero, fin6_one, fin6_two, fin6_three, fin6_four, fin6_five,
      ← BitVec.ofInt_mul, ← BitVec.ofInt_add, R43x6.shiftRight_eq, Fin.val_castLE] <;>
    congr 2 <;>
    ring


set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- **What `fd_f25519_sub` leaves**: `subFoldVec a b` at the destination, which
it also returns. No hypothesis on what it reads -- every flag in the region is
`overflow<none>`. -/
theorem sub_writes (o a b : Pointer) (s : GlobalState) (hs : s.WF)
    (ho : IsVecPtr s.mem o) (ha : IsVecPtr s.mem a) (hb : IsVecPtr s.mem b) :
    ∃ s' : GlobalState,
      StateT.run (runFunction (fd_f25519_sub.denote
          (Ctxt.Valuation.ofHVector [.value b, .value a, .value o]ₕ))) s
        = .value ([(.value o : SLLVM.Ptr)]ₕ, s')
      ∧ ({ s with mem := s.mem.splice o (vecBV (subFoldVec (readVec ha) (readVec hb))) }
          : GlobalState) ≈ s' := by
  simp only [fd_f25519_sub, Cfg.denote]
  refine Firedancer.run_runFunction' _ ?_
  refine ⟨{ s with mem := s.mem.splice o (vecBV (subFoldVec (readVec ha) (readVec hb))) },
    ?_, GlobalState.Equiv.symm (killFrom_equiv_of_none fun q hq =>
      live?_splice_eq_none (hs q hq))⟩
  obtain ⟨blkA, hblkA, hlenA⟩ := ha.1
  have hliveA : s.mem.live? a.id = some blkA := by simp only [MemoryState.live?, hblkA]
  obtain ⟨blkB, hblkB, hlenB⟩ := hb.1
  have hliveB : s.mem.live? b.id = some blkB := by simp only [MemoryState.live?, hblkB]
  denote_step_all v 7
  denote_eval v 0 7
  -- the eight constants, in the `toBitVecValue` form the fold lemmas take
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
  subst hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7
  peel_load (.vector 8 (.bitvec (.concrete 64))), blkA, a, hblkA, s
  rw [unflatten_readVec_512 ha hliveA]
  peel_load (.vector 8 (.bitvec (.concrete 64))), blkB, b, hblkB, s
  rw [unflatten_readVec_512 hb hliveB]
  denote_step_all v 19
  denote_eval v 10 19
  -- `fd_r43x6_sub_fast`: the difference, then the constant `p` with the bias
  -- already taken out of it
  rw [show (toBitVecValue 64 #v[8795933638637, 8796091973631, 8796091973631, 8796091973631,
      8796091973631, 1099510579199, 0, 0]) = toBitVecValue 64 subFastConst from rfl] at hv11
  have h10 : v10 = (Vector.ofFn fun i : Fin 8 =>
      (readVec ha)[i.val] - (readVec hb)[i.val]).map PoisonOr.value := by
    rw [hv10]
    exact denote_vec_sub _ _
  have h11 : v11 = (subFastVec (readVec ha) (readVec hb)).map PoisonOr.value := by
    rw [hv11, h10, ← subFastVec_eq]
    exact denote_vec_add_const _ _
  rw [h11] at hv12 hv13
  -- `fd_r43x6_fold_signed`, in this region's instruction order
  have h19 : v19 = (subFoldVec (readVec ha) (readVec hb)).map PoisonOr.value :=
    denote_acpBiasVec_permBias hv12 hv13 hv14 hv15 hv16 hv17 hv18 hv19
  subst h19
  peel_store (subFoldVec (readVec ha) (readVec hb)), o, ho.left, s
  simp_return


/-! ## The two callees, composed -/

/-- **The bridge.** The difference is one of the two patterns `fd_f25519_is_zero`
tests exactly when the two operands are the same element: `pVec` when they are
(reduced representations being unique), and neither when they are not (both
patterns decode to `0`). -/
theorem subFoldVec_pattern_iff' {x y : Vector (BitVec 64) 8}
    (hx : Limbs43 x) (hy : Limbs43 y) (hxy : R43x6.decode' x < R43x6.decode' y + p)
    (hyx : R43x6.decode' y < R43x6.decode' x + p) :
    (subFoldVec x y = zeroVec ∨ subFoldVec x y = pVec) ↔ vecValue x = vecValue y := by
  constructor
  · rintro (h | h)
    · have hv := vecValue_subFoldVec_reduced hx hy
      rw [h, vecValue_zeroVec] at hv
      exact sub_eq_zero.mp hv.symm
    · have hv := vecValue_subFoldVec_reduced hx hy
      rw [h, vecValue_pVec] at hv
      exact sub_eq_zero.mp hv.symm
  · intro h
    exact Or.inr (subFoldVec_of_extractLimbs_eq hx hy (extractLimbs_eq_of_value_eq' hx hy hxy hyx h))

theorem subFoldVec_pattern_iff {x y : Vector (BitVec 64) 8}
    (hx : R43x6.Reduced x) (hy : R43x6.Reduced y) :
    (subFoldVec x y = zeroVec ∨ subFoldVec x y = pVec) ↔ vecValue x = vecValue y :=
  have hbx := reduced_decode'_bounds hx
  have hby := reduced_decode'_bounds hy
  subFoldVec_pattern_iff' (reduced_limb_bounds hx) (reduced_limb_bounds hy) (by omega) (by omega)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- `fd_f25519_eq_conforms` for any operands the difference's pattern test decides. -/
theorem fd_f25519_eq_conforms' (p q : Pointer) (s : GlobalState) (hs : s.WF)
    (hp : IsVecPtr s.mem p) (hq : IsVecPtr s.mem q)
    (hpat : (subFoldVec (readVec hp) (readVec hq) = zeroVec ∨
      subFoldVec (readVec hp) (readVec hq) = pVec) ↔ vecValue (readVec hp) = vecValue (readVec hq)) :
    ∃ s' : GlobalState,
      StateT.run (runFunction (fd_f25519_eq.denote
          (Ctxt.Valuation.ofPair (.value q) (.value p)))) s
        = .value ([(.value (if vecValue (readVec hp) = vecValue (readVec hq) then 1#32 else 0#32)
            : LLVM.IntW 32)]ₕ, s') ∧ s ≈ s' := by
  simp only [Cfg.denote]
  -- `fd_f25519_t r[1]`
  obtain ⟨r, sAlloc, hrdef, hsAlloc, hsAllocWF, hrfits, hrid, hroff, -, -⟩ :=
    GlobalState.exists_afterAlloca_facts s hs (8 * 64)
  have fb : FrameBelow s.alloc.nextFreeBlock s sAlloc :=
    hsAlloc ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
  have hr₁ : IsVecPtr sAlloc.mem r := ⟨hrfits, by rw [hroff]; simp⟩
  have hlive : ∀ t : Pointer, IsVecPtr s.mem t → sAlloc.mem.live? t.id = s.mem.live? t.id :=
    fun t ht => fb t.id (lt_nextFreeBlock_of_fits hs ht.left)
  obtain ⟨hp₁, hpv⟩ := readVec_of_live?_eq (hlive p hp) hp
  obtain ⟨hq₁, hqv⟩ := readVec_of_live?_eq (hlive q hq) hq
  -- `fd_f25519_sub( r, a, b )`
  obtain ⟨substate, hsubstate, hsubstate_eq⟩ := sub_writes r p q sAlloc hsAllocWF hr₁ hp₁ hq₁
  have hsubWF : substate.WF := GlobalState.WF.of_equiv hsAllocWF.splice hsubstate_eq
  obtain ⟨hr₂, hrv⟩ := readVec_of_live?_eq (hsubstate_eq.live r.id).symm
    (isVecPtr_splice (q := r) (x := vecBV (subFoldVec (readVec hp₁) (readVec hq₁))) hr₁)
  have hrval : readVec hr₂ = subFoldVec (readVec hp) (readVec hq) := by
    rw [hrv, readVec_eq_of (readVec?_splice_self _ hr₁), hpv, hqv]
  -- `fd_f25519_is_zero( r )`
  obtain ⟨iszerostate, hiszerostate, hiszerostate_eq⟩ := isZero_pattern r substate hsubWF hr₂
  -- the frame holds only `r`, so popping it restores `s`
  have fbZero : FrameBelow s.alloc.nextFreeBlock s iszerostate :=
    FrameBelow.of_equiv hiszerostate_eq
      (FrameBelow.of_equiv hsubstate_eq (FrameBelow.splice (by rw [hrid]) fb))
  refine ⟨s.popFrame iszerostate.mem, run_runFunction (s' := iszerostate) ?_,
    GlobalState.Equiv.symm (FrameBelow.popFrame_equiv hs fbZero)⟩
  denote_step_reduce v 0 [LLVM.const?]
  peel_alloca from s as sAlloc with hsAlloc
  peel_lifetime
  rw [BlockCom.run_bind_denote_call_cfg_of_value (c := fd_f25519_sub)
    (argTys := [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr])
    (argVals := (PoisonOr.value q ::ₕ PoisonOr.value p ::ₕ PoisonOr.value r ::ₕ HVector.nil))
    (x := PoisonOr.value r) (s' := substate)
    (by simp only [simp_spine, Ctxt.Valuation.ofPair, hrdef]) hsubstate]
  rw [BlockCom.run_bind_denote_call_cfg_of_value (c := fd_f25519_is_zero)
    (argTys := [SLLVM.Ty.ptr])
    (argVals := (PoisonOr.value r ::ₕ HVector.nil))
    (x := PoisonOr.value (if readVec hr₂ = zeroVec ∨ readVec hr₂ = pVec then 1#32 else 0#32))
    (s' := iszerostate)
    (by simp only [simp_spine, Ctxt.Valuation.ofPair, hrdef]) hiszerostate]
  peel_lifetime
  simp_return
  rw [hrval]
  simp only [hpat]

theorem fd_f25519_eq_conforms (p q : Pointer) (s : GlobalState) (hs : s.WF)
    (hp : IsVecPtr s.mem p) (hq : IsVecPtr s.mem q) :
    fd_f25519_eq_spec p q s hp hq := fun hpRed hqRed =>
  fd_f25519_eq_conforms' p q s hs hp hq (subFoldVec_pattern_iff hpRed hqRed)


end Firedancer.Avx512

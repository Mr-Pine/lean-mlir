/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_r43x6_unpack
import SSA.Projects.Firedancer.Avx512.Proof.Quad
import SSA.Projects.Firedancer.MLIR.DenoteStep

/-!
# `fd_r43x6_unpack` conforms to its spec

Header only. The region is a byte permute (`vpermb` as a 64-lane
`shufflevector` over the bitcast vector), a lane-wise shift and a mask. The
work is showing that the three together cut bits `[43j, 43j+43)` out of the
`uint256`; the value equality, the limb bounds and the two range refinements
all follow from that.

The two `llvm.bitcast`s the permute is spelled with are `SLLVM.bitcast_bytes`
(a `<8 x i64>` cut into bytes) and `SLLVM.bitcast_join` (eight bytes back
together), in `SLLVM/Dialect/Semantics/MemoryLemmas.lean`. The first is where
*partial* poison matters -- the region's source vector has three poison lanes,
which the permute never reads.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine
open InstCombine.LLVM.Ty

/-! ## The bytes of the input

`ub u k` is byte `k` of the `uint256`: the region's permute reads bytes `0`
to `31` and, for the padding lanes, byte `63` -- which the `insertelement`
put there as zero. -/

/-- The `uint256` as one 256-bit word, lane `0` in the low bits -- the twin of
the spec's `wvNat`, bridged by `toNat_wvBV`. It stays here rather than beside
`wvNat`: `bv_decide` collects `u[i]` written in two different files as two
distinct atoms, so the word and the bytes cut from it have to be elaborated
together. -/
private def wvBV (u : Vector (BitVec 64) 4) : BitVec 256 :=
  u[3] ++ u[2] ++ u[1] ++ u[0]

/-- Byte `k` of the `wv_t`, zero past the 32 bytes it holds. -/
private def ub (u : Vector (BitVec 64) 4) (k : Nat) : BitVec 8 :=
  match k / 8 with
  | 0 => u[0].extractLsb' (8 * (k % 8)) 8
  | 1 => u[1].extractLsb' (8 * (k % 8)) 8
  | 2 => u[2].extractLsb' (8 * (k % 8)) 8
  | 3 => u[3].extractLsb' (8 * (k % 8)) 8
  | _ => 0

/-- The eight lanes the byte permute leaves, before the shift and mask:
lane `j` is the seven-or-eight byte window the shuffle mask selects. -/
private def v10lanes (u : Vector (BitVec 64) 4) : Vector (BitVec 64) 8 :=
  #v[0#0 ++ ub u 63 ++ ub u 63 ++ ub u 5 ++ ub u 4 ++ ub u 3 ++ ub u 2 ++ ub u 1 ++ ub u 0,
     0#0 ++ ub u 63 ++ ub u 63 ++ ub u 10 ++ ub u 9 ++ ub u 8 ++ ub u 7 ++ ub u 6 ++ ub u 5,
     0#0 ++ ub u 63 ++ ub u 16 ++ ub u 15 ++ ub u 14 ++ ub u 13 ++ ub u 12 ++ ub u 11 ++ ub u 10,
     0#0 ++ ub u 63 ++ ub u 63 ++ ub u 21 ++ ub u 20 ++ ub u 19 ++ ub u 18 ++ ub u 17 ++ ub u 16,
     0#0 ++ ub u 63 ++ ub u 63 ++ ub u 26 ++ ub u 25 ++ ub u 24 ++ ub u 23 ++ ub u 22 ++ ub u 21,
     0#0 ++ ub u 63 ++ ub u 63 ++ ub u 31 ++ ub u 30 ++ ub u 29 ++ ub u 28 ++ ub u 27 ++ ub u 26,
     0#0 ++ ub u 63 ++ ub u 63 ++ ub u 63 ++ ub u 63 ++ ub u 63 ++ ub u 63 ++ ub u 63 ++ ub u 63,
     0#0 ++ ub u 63 ++ ub u 63 ++ ub u 63 ++ ub u 63 ++ ub u 63 ++ ub u 63 ++ ub u 63 ++ ub u 63]

/-- The six limbs the region is specified to cut, as `BitVec`s: bits
`[43j, 43j+43)` of the word, zero in lanes 6 and 7. -/
private def unpackVec (u : Vector (BitVec 64) 4) : Vector (BitVec 64) 8 :=
  #v[((wvBV u).extractLsb' 0 43).setWidth 64,
     ((wvBV u).extractLsb' 43 43).setWidth 64,
     ((wvBV u).extractLsb' 86 43).setWidth 64,
     ((wvBV u).extractLsb' 129 43).setWidth 64,
     ((wvBV u).extractLsb' 172 43).setWidth 64,
     ((wvBV u).extractLsb' 215 43).setWidth 64,
     0, 0]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
/-- **Limb derivation** for `fd_r43x6_unpack`: the denotation is the limb
vector `unpackVec u`, with no hypothesis on `u`. -/
theorem denote_fd_r43x6_unpack (u : Vector (BitVec 64) 4) :
    fd_r43x6_unpack.denote (Ctxt.Valuation.singleton (u.map PoisonOr.value))
      = ([(unpackVec u).map PoisonOr.value]ₕ :
        HVector TyDenote.toType [SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64)))]) := by
  unfold fd_r43x6_unpack
  denote_step_reduce v 7 [LLVM.const?] fold
  -- `%6`/`%7`: the four input lanes, three poison lanes and the zero the
  -- `insertelement` writes into lane 7.
  have v7Value : v7 = #v[.value u[0], .value u[1], .value u[2], .value u[3],
      .poison, .poison, .poison, .value 0#64] := by
    simp [hv7, LLVM.Ty.insertelement, LLVM.Ty.shufflevector, LLVM.Ty.poison]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [Ctxt.Valuation.singleton]
  subst v7Value
  denote_step_all v 12
  denote_eval v 8 12
  -- `%8`: the vector read as bytes. Bytes 32-55 are poison -- lanes 4, 5 and
  -- 6 of `%7` are -- and the permute reads none of them.
  have hb : ∀ (k : Nat) (hk : k < 32), (ofVector v8)[k]'(by omega) = .value (ub u k) := by
    intro k hk
    rw [hv8, SLLVM.bitcast_bytes]
    have h8 : k / 8 = 0 ∨ k / 8 = 1 ∨ k / 8 = 2 ∨ k / 8 = 3 := by omega
    rcases h8 with h | h | h | h <;> simp [ub, h]
  have hb63 : (ofVector v8)[63] = .value (ub u 63) := by
    rw [hv8, SLLVM.bitcast_bytes]
    simp [ub]
  -- `%9`: the permute, reading bytes 0-31 and the zero byte 63.
  have v9Value : v9 = #v[.value (ub u 0), .value (ub u 1), .value (ub u 2), .value (ub u 3), .value (ub u 4), .value (ub u 5), .value (ub u 63), .value (ub u 63),
      .value (ub u 5), .value (ub u 6), .value (ub u 7), .value (ub u 8), .value (ub u 9), .value (ub u 10), .value (ub u 63), .value (ub u 63),
      .value (ub u 10), .value (ub u 11), .value (ub u 12), .value (ub u 13), .value (ub u 14), .value (ub u 15), .value (ub u 16), .value (ub u 63),
      .value (ub u 16), .value (ub u 17), .value (ub u 18), .value (ub u 19), .value (ub u 20), .value (ub u 21), .value (ub u 63), .value (ub u 63),
      .value (ub u 21), .value (ub u 22), .value (ub u 23), .value (ub u 24), .value (ub u 25), .value (ub u 26), .value (ub u 63), .value (ub u 63),
      .value (ub u 26), .value (ub u 27), .value (ub u 28), .value (ub u 29), .value (ub u 30), .value (ub u 31), .value (ub u 63), .value (ub u 63),
      .value (ub u 63), .value (ub u 63), .value (ub u 63), .value (ub u 63), .value (ub u 63), .value (ub u 63), .value (ub u 63), .value (ub u 63),
      .value (ub u 63), .value (ub u 63), .value (ub u 63), .value (ub u 63), .value (ub u 63), .value (ub u 63), .value (ub u 63), .value (ub u 63)] := by
    rw [hv9, hv5]
    apply Vector.ext (n := 64)
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.shufflevector, LLVM.Ty.poison, hb, hb63]
  -- `%10`: the bytes read back as six 43-bit windows, one per lane, plus the
  -- two zero lanes.
  have hdef : LLVM.Ty.Defined SLLVM.v64i8 v9 := by
    rw [v9Value]
    intro i
    fin_cases i <;> exact PoisonOr.value_ne_poison _
  have v10Value : v10 = (v10lanes u).map PoisonOr.value := by
    rw [hv10, SLLVM.bitcast_join _ hdef]
    apply Vector.ext (n := 8)
    intro j hj
    interval_cases j <;>
      simp [Vector.getElem_ofFn, BitVec.packLanes_bytes8, v9Value, SLLVM.byteOf, v10lanes]
  -- `%11`/`%12`: the lane-wise shift and the 43-bit mask.
  have v12Value : v12 = (unpackVec u).map PoisonOr.value := by
    rw [hv12, hv11, v10Value, hv1, hv0]
    apply Vector.ext (n := 8)
    intro j hj
    interval_cases j <;>
      (simp [InstCombine.binaryDenote, LLVM.lshr, LLVM.lshr?, LLVM.and, LLVM.and?,
         LLVM.Ty.dense, Vector.getElem_map]
       simp only [v10lanes, unpackVec, wvBV, ub, Vector.getElem_mk, List.getElem_toArray,
         List.getElem_cons_zero, List.getElem_cons_succ]
       bv_decide)
  subst v12Value
  simp_denote_only

/-! ## From the limbs to the header's contract

Every clause of the specification is the limb equation
`limb j = ⌊u / 2^43j⌋ mod 2^43` read at a different width. -/

/-- Splitting off the low 64-bit lane of an append. -/
private theorem toNat_append64 {m : Nat} (x : BitVec m) (y : BitVec 64) :
    (x ++ y).toNat = x.toNat * 2 ^ 64 + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

/-- The two readings of a `wv_t` agree. -/
private theorem toNat_wvBV (u : Vector (BitVec 64) 4) : (wvBV u).toNat = wvNat u := by
  simp only [wvBV, wvNat, toNat_append64]
  ring

/-- **The limb equation.** Limb `j` is bits `[43j, 43j+43)` of the `uint256`. -/
private theorem toNat_unpackVec (u : Vector (BitVec 64) 4) (j : Nat) (hj : j < 6) :
    ((unpackVec u)[j]'(by omega)).toNat = wvNat u / 2 ^ (43 * j) % 2 ^ 43 := by
  have hw := toNat_wvBV u
  interval_cases j <;>
    (simp [unpackVec, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat,
       Nat.shiftRight_eq_div_pow, hw]
     omega)

/-- ... and so it fits, which is what makes `toInt` read it back. -/
private theorem toInt_unpackVec (u : Vector (BitVec 64) 4) (j : Nat) (hj : j < 6) :
    ((unpackVec u)[j]'(by omega)).toInt = ((wvNat u / 2 ^ (43 * j) % 2 ^ 43 : ℕ) : ℤ) := by
  rw [toInt_of_lt (by rw [toNat_unpackVec u j hj]; omega), toNat_unpackVec u j hj]

/-- Limb `i` of the result, over ℕ. -/
private theorem extractLimbs_eq (u : Vector (BitVec 64) 4) (i : Fin R43x6.limbCount) :
    R43x6.extractLimbs (unpackVec u) i
      = ((wvNat u / 2 ^ (43 * i.val) % 2 ^ 43 : ℕ) : ℤ) := by
  show ((unpackVec u)[i.val]'_).toInt = _
  exact toInt_unpackVec u i.val
    (by have := i.isLt; simp only [R43x6.limbCount] at this; omega)

/-- **The value.** The six limbs decode to the `uint256` they were cut from. -/
private theorem decode'_unpackVec (u : Vector (BitVec 64) 4) :
    R43x6.decode' (unpackVec u) = (wvNat u : ℤ) := by
  rw [← R43x6.decodeLimbs_extractLimbs, R43x6.decodeLimbs_eq]
  simp only [extractLimbs_eq, show ((0 : Fin R43x6.limbCount) : ℕ) = 0 from rfl,
    show ((1 : Fin R43x6.limbCount) : ℕ) = 1 from rfl,
    show ((2 : Fin R43x6.limbCount) : ℕ) = 2 from rfl,
    show ((3 : Fin R43x6.limbCount) : ℕ) = 3 from rfl,
    show ((4 : Fin R43x6.limbCount) : ℕ) = 4 from rfl,
    show ((5 : Fin R43x6.limbCount) : ℕ) = 5 from rfl]
  have := wvNat_lt u
  push_cast
  omega

/-- **The class.** Limbs 0-4 in `[0,2^43)`, limb 5 in `[0,2^41)`: the word has
only 256 bits, so the top limb is 41 of them. -/
private theorem unpacked_unpackVec (u : Vector (BitVec 64) 4) :
    R43x6.Unpacked (unpackVec u) := by
  have hlt := wvNat_lt u
  refine ⟨fun i _ => ?_, ?_⟩
  · rw [extractLimbs_eq]
    refine ⟨by positivity, ?_⟩
    have h : wvNat u / 2 ^ (43 * i.val) % 2 ^ 43 < 2 ^ 43 := Nat.mod_lt _ (by norm_num)
    exact_mod_cast h
  · rw [extractLimbs_eq, show ((5 : Fin R43x6.limbCount) : ℕ) = 5 from rfl]
    refine ⟨by positivity, ?_⟩
    have h : wvNat u / 2 ^ (43 * 5) % 2 ^ 43 < 2 ^ 41 := by omega
    exact_mod_cast h

theorem fd_r43x6_unpack_conforms (u : Vector (BitVec 64) 4) : fd_r43x6_unpack_spec u := by
  have hdec := decode'_unpackVec u
  have hunp := unpacked_unpackVec u
  refine ⟨unpackVec u, ?_, hunp, hdec, rfl, rfl, ?_, ?_⟩
  · rw [denote_fd_r43x6_unpack]
    rfl
  · intro h
    exact ⟨hunp.1, hunp.2, by rw [hdec]; exact_mod_cast h⟩
  · intro h
    refine ⟨hunp.1, ⟨hunp.2.1, ?_⟩, by rw [hdec]; exact_mod_cast h⟩
    rw [extractLimbs_eq, show ((5 : Fin R43x6.limbCount) : ℕ) = 5 from rfl]
    have hp : wvNat u < 2 ^ 255 - 19 := by simpa [p] using h
    have h40 : wvNat u / 2 ^ (43 * 5) % 2 ^ 43 < 2 ^ 40 := by omega
    exact_mod_cast h40

end Firedancer.Avx512

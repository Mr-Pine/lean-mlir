/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_neg
public import SSA.Projects.Firedancer.MLIR.DenoteStep
public import SSA.Projects.Firedancer.Proof.Memory
public import SSA.Projects.Firedancer.Proof.Tactics
public import SSA.Projects.Firedancer.Avx512.Proof.Common
public import SSA.Projects.Firedancer.Avx512.Proof.Quad
public import SSA.Projects.Firedancer.Avx512.Proof.Step.Basic

/-!
# `fd_ed25519_point_neg` conformance (AVX-512)

The region is `negQuad` -- a lane subtract from `2p` -- then the QUAD fold,
which `Proof/Quad.lean`'s `denote_quadFold_*` already model instruction for
instruction. It stores five vectors into `r`: the pre-fold `03` and `14`, then
all three folded ones; `negMem_equiv` collapses those into the one `Quad.BV`
splice the spec states. `run_runFunction'` comes first; the output QUAD and its
properties are supplied once the region has returned.

The lane lemmas unfold `negQuad` through the `rfl` projections `negQuad_v03`
and friends, never by `rfl` on `vectorFunc`: the kernel would unfold
`2p - x` into `Nat.add` on the 44-bit literal and recurse on it.
-/

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

namespace PointNeg

/-- **`FD_R43X6_QUAD_LANE_SUB_FAST`'s result**, before the fold: `2p - a` on the
`X` and `T` lanes (`0, 3, 4, 7`), `a` itself on the `Y` and `Z` lanes. -/
def negQuad (q : Quad) : Quad where
  v03 := #v[17592186044378#64 - q.v03[0], q.v03[1], q.v03[2], 17592186044378#64 - q.v03[3],
    17592186044414#64 - q.v03[4], q.v03[5], q.v03[6], 17592186044414#64 - q.v03[7]]
  v14 := #v[17592186044414#64 - q.v14[0], q.v14[1], q.v14[2], 17592186044414#64 - q.v14[3],
    17592186044414#64 - q.v14[4], q.v14[5], q.v14[6], 17592186044414#64 - q.v14[7]]
  v25 := #v[17592186044414#64 - q.v25[0], q.v25[1], q.v25[2], 17592186044414#64 - q.v25[3],
    2199023255550#64 - q.v25[4], q.v25[5], q.v25[6], 2199023255550#64 - q.v25[7]]

/-- `%25`: `2p`'s limbs 0 and 3 on the `X`/`T` lanes, poison on the `Y`/`Z`
lanes, which the shuffle after the `sub` never reads. -/
def negC03 : Vector (LLVM.IntW 64) 8 :=
  #v[.value 17592186044378#64, .poison, .poison, .value 17592186044378#64,
     .value 17592186044414#64, .poison, .poison, .value 17592186044414#64]

/-- `%34`: limbs 1 and 4. -/
def negC14 : Vector (LLVM.IntW 64) 8 :=
  #v[.value 17592186044414#64, .poison, .poison, .value 17592186044414#64,
     .value 17592186044414#64, .poison, .poison, .value 17592186044414#64]

/-- `%43`: limbs 2 and 5. -/
def negC25 : Vector (LLVM.IntW 64) 8 :=
  #v[.value 17592186044414#64, .poison, .poison, .value 17592186044414#64,
     .value 2199023255550#64, .poison, .poison, .value 2199023255550#64]

set_option maxHeartbeats 1000000 in
/-- **`%58`/`%59`, one vector's lane subtract**: `c - x` on the `X`/`T` lanes,
`x` on the others. The minuend's poison lanes are exactly the ones the shuffle
takes from `x`. -/
theorem denote_negLanes {x : Vector (BitVec 64) 8} {c d : BitVec 64}
    {m t u : Vector (LLVM.IntW 64) 8}
    (hm : m = #v[.value c, .poison, .poison, .value c, .value d, .poison, .poison, .value d])
    (ht : t = Vector.ofFn fun i : Fin 8 =>
      InstCombine.binaryDenote InstCombine.MOp.BinaryOp.sub m[i.val] (x.map PoisonOr.value)[i.val])
    (hu : u = LLVM.Ty.shufflevector (e := .bitvec (.concrete 64))
      [0, 9, 10, 3, 4, 13, 14, 7] t (x.map PoisonOr.value)) :
    u = (#v[c - x[0], x[1], x[2], c - x[3], d - x[4], x[5], x[6], d - x[7]]
      : Vector (BitVec 64) 8).map PoisonOr.value := by
  subst hm ht hu
  apply Vector.ext
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i <;>
    simp [LLVM.Ty.shufflevector, InstCombine.binaryDenote, LLVM.sub, LLVM.sub?]

/-- The five stores the region makes, in program order: the pre-fold `03` and
`14` vectors, then the three folded ones. -/
def negMem (m : MemoryState) (r : Pointer) (q : Quad) : MemoryState :=
  ((((m.splice r (vecBV (negQuad q).v03)).splice (r.withOffset 64) (vecBV (negQuad q).v14)).splice
    r (vecBV (foldQuad (negQuad q)).v03)).splice (r.withOffset 64)
    (vecBV (foldQuad (negQuad q)).v14)).splice (r.withOffset 128) (vecBV (foldQuad (negQuad q)).v25)

/-! ### The five stores are one -/

/-- Stores to disjoint ranges commute. -/
theorem spliceBits_comm {n w w' : Nat} (bytes : BitVec n) (off off' : Nat)
    (x : BitVec w) (y : BitVec w') (h : off + w ≤ off' ∨ off' + w' ≤ off) :
    spliceBits (spliceBits bytes off x) off' y = spliceBits (spliceBits bytes off' y) off x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [getLsbD_spliceBits]
  split_ifs <;> first | rfl | omega

/-- The region's five stores, at the bit level: the two pre-fold writes are
overwritten, and the three folded ones are adjacent. -/
theorem spliceBits_negChain {n : Nat} (bytes : BitVec n) (o : Nat)
    (a03 a14 b03 b14 b25 : BitVec 512) :
    spliceBits (spliceBits (spliceBits (spliceBits (spliceBits bytes o a03) (o + 512) a14)
      o b03) (o + 512) b14) (o + 1024) b25 = spliceBits bytes o (b25 ++ b14 ++ b03) := by
  rw [spliceBits_comm (spliceBits bytes o a03) (o + 512) o a14 b03 (.inr (by omega)),
    spliceBits_spliceBits_self, spliceBits_spliceBits_self, spliceBits_append, spliceBits_append]

set_option maxRecDepth 20000 in
theorem zero_append3 (a b c : BitVec 512) :
    (0#(512 * 0) ++ a ++ b ++ c : BitVec (3 * 8 * 64)) = a ++ b ++ c := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft,
    Nat.zero_or]

theorem BV_eq_append (q : Quad) : q.BV = vecBV q.v25 ++ vecBV q.v14 ++ vecBV q.v03 := by
  rw [Quad.BV_append]; exact zero_append3 _ _ _

/-- A store through a field pointer changes the base pointer's block. -/
theorem live?_splice_withOffset {m : MemoryState} {p : Pointer} {b : LiveBlock}
    (hb : m.live? p.id = some b) {w : Nat} (d : BitVec w) (o : BitVec 64) :
    (m.splice (p.withOffset o) d).live? p.id
      = some { length := b.length, bytes := spliceBits b.bytes (p.withOffset o).offsetInBits d } :=
  splicedLive m (p.withOffset o) b hb d

/-- **The five stores are one `Quad.BV` store.** -/
theorem negMem_equiv {s : GlobalState} {r : Pointer} (q : Quad)
    (h64 : (r.withOffset 64).offsetInBits = r.offsetInBits + 512)
    (h128 : (r.withOffset 128).offsetInBits = r.offsetInBits + 1024) :
    ({ s with mem := negMem s.mem r q } : GlobalState)
      ≈ { s with mem := s.mem.splice r (foldQuad (negQuad q)).BV } := by
  refine ⟨rfl, rfl, fun c => ?_⟩
  dsimp only
  by_cases hc : r.id = c
  · subst hc
    cases hl : s.mem.live? r.id with
    | none =>
      have e1 : (s.mem.splice r (vecBV (negQuad q).v03)).live? r.id = none := splicedDead hl
      have e2 : ((s.mem.splice r (vecBV (negQuad q).v03)).splice (r.withOffset 64)
          (vecBV (negQuad q).v14)).live? r.id = none := splicedDead e1
      have e3 := splicedDead (p := r) (x := vecBV (foldQuad (negQuad q)).v03) e2
      have e4 : ((((s.mem.splice r (vecBV (negQuad q).v03)).splice (r.withOffset 64)
          (vecBV (negQuad q).v14)).splice r (vecBV (foldQuad (negQuad q)).v03)).splice
          (r.withOffset 64) (vecBV (foldQuad (negQuad q)).v14)).live? r.id = none :=
        splicedDead e3
      have e5 : (negMem s.mem r q).live? r.id = none := splicedDead e4
      rw [e5, splicedDead hl]
    | some blk =>
      have e1 := splicedLive s.mem r blk hl (vecBV (negQuad q).v03)
      have e2 := live?_splice_withOffset e1 (vecBV (negQuad q).v14) 64
      have e3 := splicedLive _ r _ e2 (vecBV (foldQuad (negQuad q)).v03)
      have e4 := live?_splice_withOffset e3 (vecBV (foldQuad (negQuad q)).v14) 64
      have e5 := live?_splice_withOffset e4 (vecBV (foldQuad (negQuad q)).v25) 128
      simp only [negMem]
      rw [e5, splicedLive s.mem r blk hl, h64, h128, spliceBits_negChain, BV_eq_append]
  · simp only [negMem]
    rw [live?_splice_ne (p := r.withOffset 128) hc, live?_splice_ne (p := r.withOffset 64) hc,
      live?_splice_ne (p := r) hc, live?_splice_ne (p := r.withOffset 64) hc,
      live?_splice_ne (p := r) hc, live?_splice_ne (p := r) hc]

/-! ### What the lane subtract computes -/

theorem vectorFunc_negQuad_Y (q : Quad) : (negQuad q).vectorFunc 1 = q.vectorFunc 1 := by
  funext k; fin_cases k <;> rfl

theorem vectorFunc_negQuad_Z (q : Quad) : (negQuad q).vectorFunc 2 = q.vectorFunc 2 := by
  funext k; fin_cases k <;> rfl

theorem toNat_lit_sub {c : ℕ} {x : BitVec 64} (hc : c < 2 ^ 64) (h : x.toNat ≤ c) :
    (BitVec.ofNat 64 c - x).toNat = c - x.toNat := by
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]; exact h),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]

theorem negQuad_v03 (q : Quad) : (negQuad q).v03 =
    #v[17592186044378#64 - q.v03[0], q.v03[1], q.v03[2], 17592186044378#64 - q.v03[3],
      17592186044414#64 - q.v03[4], q.v03[5], q.v03[6], 17592186044414#64 - q.v03[7]] := rfl
theorem negQuad_v14 (q : Quad) : (negQuad q).v14 =
    #v[17592186044414#64 - q.v14[0], q.v14[1], q.v14[2], 17592186044414#64 - q.v14[3],
      17592186044414#64 - q.v14[4], q.v14[5], q.v14[6], 17592186044414#64 - q.v14[7]] := rfl
theorem negQuad_v25 (q : Quad) : (negQuad q).v25 =
    #v[17592186044414#64 - q.v25[0], q.v25[1], q.v25[2], 17592186044414#64 - q.v25[3],
      2199023255550#64 - q.v25[4], q.v25[5], q.v25[6], 2199023255550#64 - q.v25[7]] := rfl

theorem vectorFunc_eq_quadLimb (q : Quad) (j : Fin 4) :
    q.vectorFunc j = quadLimb q.v03 q.v14 q.v25 j :=
  laneFunc_vector q j

theorem vectorFunc_negQuad_X (q : Quad) (hb : q.NegBounds 0) (k : Fin 6) :
    (negQuad q).vectorFunc 0 k = twoPLimb k - q.vectorFunc 0 k := by
  have h := hb k
  rw [vectorFunc_eq_quadLimb] at h ⊢
  rw [vectorFunc_eq_quadLimb, negQuad_v03, negQuad_v14, negQuad_v25]
  fin_cases k <;>
    simp only [quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat, Fin.isValue, twoPLimb,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] at h ⊢ <;>
    exact toNat_lit_sub (by norm_num) h

theorem vectorFunc_negQuad_T (q : Quad) (hb : q.NegBounds 3) (k : Fin 6) :
    (negQuad q).vectorFunc 3 k = twoPLimb k - q.vectorFunc 3 k := by
  have h := hb k
  rw [vectorFunc_eq_quadLimb] at h ⊢
  rw [vectorFunc_eq_quadLimb, negQuad_v03, negQuad_v14, negQuad_v25]
  fin_cases k <;>
    simp only [quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat, Fin.isValue, twoPLimb,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] at h ⊢ <;>
    exact toNat_lit_sub (by norm_num) h

/-- Limbwise `2p - x`, with no limb wrapping, is `-x`. -/
theorem decodeNat_twoP_sub {x y : Fin 6 → ℕ} (hy : ∀ k, y k = twoPLimb k - x k)
    (hb : ∀ k, x k ≤ twoPLimb k) :
    ((decodeNat y : ℕ) : ZMod p) = -((decodeNat x : ℕ) : ZMod p) := by
  have hsum : decodeNat y + decodeNat x = 2 * p := by
    have h0 := hb 0; have h1 := hb 1; have h2 := hb 2
    have h3 := hb 3; have h4 := hb 4; have h5 := hb 5
    simp only [decodeNat_eq, hy, twoPLimb, p] at *
    simp at h0 h1 h2 h3 h4 h5 ⊢
    omega
  have hz : ((decodeNat y + decodeNat x : ℕ) : ZMod p) = 0 := by
    rw [hsum]; push_cast; simp
  push_cast at hz
  exact eq_neg_of_add_eq_zero_left hz

/-- **The lane subtract negates `X` and `T`.** -/
theorem toPoint_negQuad (q : Quad) (hb0 : q.NegBounds 0) (hb3 : q.NegBounds 3) :
    (negQuad q).toPoint = ⟨-q.toPoint.X, q.toPoint.Y, q.toPoint.Z, -q.toPoint.T⟩ := by
  show Point.mk (quadElem (negQuad q) 0) (quadElem (negQuad q) 1) (quadElem (negQuad q) 2)
      (quadElem (negQuad q) 3)
    = Point.mk (-quadElem q 0) (quadElem q 1) (quadElem q 2) (-quadElem q 3)
  simp only [quadElem, vectorFunc_negQuad_Y, vectorFunc_negQuad_Z,
    decodeNat_twoP_sub (vectorFunc_negQuad_X q hb0) hb0,
    decodeNat_twoP_sub (vectorFunc_negQuad_T q hb3) hb3]

/-! ### The fold's bounds -/

/-- The fold leaves every limb within `2p`'s, whatever it was given: carries
into a limb are at most `2^21` (`19 · 2^24` for limb 0). -/
theorem foldQuad_negBounds (q : Quad) (j : Fin 4) : (foldQuad q).NegBounds j := by
  intro k
  rw [laneFunc_foldQuad]
  have hlt : ∀ k, q.vectorFunc j k < 2 ^ 64 := fun k => by
    simp only [Quad.vectorFunc, Function.comp_apply, laneFunc]; exact BitVec.isLt _
  have h0 := hlt 0; have h1 := hlt 1; have h2 := hlt 2
  have h3 := hlt 3; have h4 := hlt 4; have h5 := hlt 5
  fin_cases k <;> simp [foldLimb, twoPLimb] <;> omega

end PointNeg

open PointNeg in
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
theorem fd_ed25519_point_neg_conforms (r a : Pointer) (s : GlobalState)
    (hs : s.WF) (hne : r.id ≠ a.id)
    (hr : IsQuadPtr s.mem r) (ha : IsQuadPtr s.mem a) :
    fd_ed25519_point_neg_spec r a s hne hr ha := by
  simp only [fd_ed25519_point_neg_spec, Cfg.denote]
  intro hb0 hb3
  refine run_runFunction' _ ?_

  denote_step_reduce v 52 [LLVM.const?, LLVM.Ty.poison] fold

  -- `%0 … %52`: the three `2p` minuends and the fold's constants.
  replace hv25 : v25 = negC03 := by
    simp only [hv25]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, negC03]
  replace hv34 : v34 = negC14 := by
    simp only [hv34]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, negC14]
  replace hv43 : v43 = negC25 := by
    simp only [hv43]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, negC25]
  replace hv52 : v52 = quadMul19 := by
    simp only [hv52]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, quadMul19]
  replace hv4 : v4 = toBitVecValue 64 quadShift43 := by
    simp only [quadShift43]; denote_dense hv4
  replace hv3 : v3 = toBitVecValue 64 quadShift48 := by
    simp only [quadShift48]; denote_dense hv3
  replace hv1 : v1 = toBitVecValue 64 quadMask43 := by
    simp only [quadMask43]; denote_dense hv1
  replace hv0 : v0 = toBitVecValue 64 quadMask48 := by
    simp only [quadMask48]; denote_dense hv0
  clear hv2 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15 hv16 hv17 hv18 hv19 hv20
  clear hv21 hv22 hv23 hv24 hv26 hv27 hv28 hv29 hv30 hv31 hv32 hv33 hv35 hv36 hv37 hv38
  clear hv39 hv40 hv41 hv42 hv44 hv45 hv46 hv47 hv48 hv49 hv50 hv51

  -- `%53 … %57`: `a`'s three vectors, at 0, 64 and 128 bytes in.
  obtain ⟨ablk, hablkE, halen⟩ := ha.1
  have halive : s.mem.live? a.id = some ablk := by simp [MemoryState.live?, hablkE]
  have h64 : (64 : BitVec 64).toNat = 64 := rfl
  have h128 : (128 : BitVec 64).toNat = 128 := rfl

  peel_load (.vector 8 (.bitvec (.concrete 64))), ablk, a, hablkE, s
  rw [unflatten_readQuad_v03 ha halive]

  peel_gep 64 with a, ha.1, s as aField
  have hoffA : aField.offsetInBits = a.offsetInBits + 512 := by
    have hb := ha.2
    simp only [aField, Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add, h64] at hb ⊢
    omega
  have haFieldE : s.mem[aField.id]? = some (.live ablk) := hablkE
  peel_load (.vector 8 (.bitvec (.concrete 64))), ablk, aField, haFieldE, s
  rw [hoffA, unflatten_readQuad_v14 ha halive]

  peel_gep 128 with a, ha.1, s as aField25
  have hoffA25 : aField25.offsetInBits = a.offsetInBits + 1024 := by
    have hb := ha.2
    simp only [aField25, Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add, h128] at hb ⊢
    omega
  have haField25E : s.mem[aField25.id]? = some (.live ablk) := hablkE
  peel_load (.vector 8 (.bitvec (.concrete 64))), ablk, aField25, haField25E, s
  rw [hoffA25, unflatten_readQuad_v25 ha halive]

  -- `%58`/`%59`: the `03` lane subtract, stored to `r`.
  denote_step_reduce v 59 only [hv25] fold
  have hN03 : v59 = (negQuad (readQuad ha)).v03.map PoisonOr.value :=
    denote_negLanes rfl rfl hv59
  subst hN03
  refine name_of ({ s with mem := s.mem.splice r (vecBV (negQuad (readQuad ha)).v03) })
    fun s₁ hs₁ => ?_
  peel_store (negQuad (readQuad ha)).v03, r, hr.1, s as s₁ := hs₁
  have f₁ : Fits s₁.mem r (3 * 8 * 64) := hs₁ ▸ fits_splice hr.1

  -- `%60 … %63`: `a`'s `14` again, which the store to `r` did not reach.
  have hE₁ : s₁.mem[aField.id]? = some (.live ablk) := by
    rw [hs₁]
    exact (getElem?_splice_ne (m := s.mem) (p := r) (x := vecBV (negQuad (readQuad ha)).v03)
      (q := aField.id) hne).trans hablkE
  peel_load (.vector 8 (.bitvec (.concrete 64))), ablk, aField, hE₁, s₁
  rw [hoffA, unflatten_readQuad_v14 ha halive]
  denote_step_reduce v 62 only [hv34] fold
  have hN14 : v62 = (negQuad (readQuad ha)).v14.map PoisonOr.value :=
    denote_negLanes rfl rfl hv62
  subst hN14
  peel_gep 64 with r, f₁, s₁ as rField
  have fR : Fits s₁.mem rField 1024 := Fits.mono hrField (by simp)
  refine name_of
    ({ s₁ with mem := s₁.mem.splice rField (vecBV (negQuad (readQuad ha)).v14) })
    fun s₂ hs₂ => ?_
  peel_store (negQuad (readQuad ha)).v14, rField, fR, s₁ as s₂ := hs₂
  have f₂ : Fits s₂.mem r (3 * 8 * 64) := hs₂ ▸ fits_splice f₁

  -- `%64 … %67`: the same for `25`.
  have hE₂ : s₂.mem[aField25.id]? = some (.live ablk) := by
    rw [hs₂]
    exact (getElem?_splice_ne (m := s₁.mem) (p := rField)
      (x := vecBV (negQuad (readQuad ha)).v14) (q := aField25.id) hne).trans hE₁
  peel_load (.vector 8 (.bitvec (.concrete 64))), ablk, aField25, hE₂, s₂
  rw [hoffA25, unflatten_readQuad_v25 ha halive]
  denote_step_reduce v 66 only [hv43] fold
  have hN25 : v66 = (negQuad (readQuad ha)).v25.map PoisonOr.value :=
    denote_negLanes rfl rfl hv66
  subst hN25
  peel_gep 128 with r, f₂, s₂ as rField25
  have fR25 : Fits s₂.mem rField25 512 := Fits.mono hrField25 (by simp)

  -- `%68 … %78`: `FD_R43X6_QUAD_FOLD_UNSIGNED`, one store per vector.
  denote_step_reduce v 74 only [hv4, hv3, hv52, hv1] fold
  have hF03 : v74 = (foldQuad (negQuad (readQuad ha))).v03.map PoisonOr.value :=
    denote_quadFold_v03 (q := negQuad (readQuad ha)) rfl rfl rfl rfl hv74
  subst hF03
  refine name_of
    ({ s₂ with mem := s₂.mem.splice r (vecBV (foldQuad (negQuad (readQuad ha))).v03) })
    fun s₃ hs₃ => ?_
  peel_store (foldQuad (negQuad (readQuad ha))).v03, r, f₂, s₂ as s₃ := hs₃

  denote_step_reduce v 76 only [hv1] fold
  have hF14 : v76 = (foldQuad (negQuad (readQuad ha))).v14.map PoisonOr.value :=
    denote_quadFold_v14 (q := negQuad (readQuad ha)) hv68 rfl hv76
  subst hF14
  have f₄ : Fits s₃.mem rField (8 * 64) := by
    rw [hs₃, hs₂]; exact fits_splice (fits_splice (Fits.mono fR (by omega)))
  refine name_of
    ({ s₃ with mem := s₃.mem.splice rField (vecBV (foldQuad (negQuad (readQuad ha))).v14) })
    fun s₄ hs₄ => ?_
  peel_store (foldQuad (negQuad (readQuad ha))).v14, rField, f₄, s₃ as s₄ := hs₄

  denote_step_reduce v 78 only [hv0] fold
  have hF25 : v78 = (foldQuad (negQuad (readQuad ha))).v25.map PoisonOr.value :=
    denote_quadFold_v25 (q := negQuad (readQuad ha)) hv69 rfl hv78
  subst hF25
  have f₅ : Fits s₄.mem rField25 (8 * 64) := by
    rw [hs₄, hs₃]; exact fits_splice (fits_splice fR25)
  refine name_of
    ({ s₄ with mem := s₄.mem.splice rField25 (vecBV (foldQuad (negQuad (readQuad ha))).v25) })
    fun s₅ hs₅ => ?_
  peel_store (foldQuad (negQuad (readQuad ha))).v25, rField25, f₅, s₄ as s₅ := hs₅

  -- `return %arg0`, in `s₅`
  refine ⟨s₅, by simp_return, ?_⟩

  /- The region has returned. What remains is that its five stores are the one
  the spec states, and what that store holds. -/
  have hmem : s₅.mem = negMem s.mem r (readQuad ha) := by
    -- `unfold` + `dsimp`, not `rfl`: unification would unfold the splices
    rw [hs₅, hs₄, hs₃, hs₂, hs₁]; unfold negMem; dsimp only
  rw [hmem]

  -- `r`'s two field pointers are 512 and 1024 bits in: `hr.2` rules out wrapping
  have h64 : (r.withOffset 64).offsetInBits = r.offsetInBits + 512 := by
    have hb := hr.2
    simp only [Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add,
      show (64 : BitVec 64).toNat = 64 from rfl] at hb ⊢
    omega
  have h128 : (r.withOffset 128).offsetInBits = r.offsetInBits + 1024 := by
    have hb := hr.2
    simp only [Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add,
      show (128 : BitVec 64).toNat = 128 from rfl] at hb ⊢
    omega
  -- the region allocates nothing, so the frame kill at `return` is invisible
  have hnone : ∀ c : BlockId, s.alloc.nextFreeBlock ≤ c.id →
      (negMem s.mem r (readQuad ha)).live? c = none := fun c hc => by
    unfold negMem
    exact live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none
      (live?_splice_eq_none (live?_splice_eq_none (hs c hc)))))
  have hkill := killFrom_equiv_of_none (s := s) (m := negMem s.mem r (readQuad ha)) hnone
  have hcol := negMem_equiv (s := s) (readQuad ha) h64 h128

  exact ⟨foldQuad (negQuad (readQuad ha)),
    GlobalState.Equiv.trans (GlobalState.Equiv.symm hcol) (GlobalState.Equiv.symm hkill),
    by rw [toPoint_foldQuad, toPoint_negQuad _ hb0 hb3], foldQuad_negBounds _⟩

end Firedancer.Avx512

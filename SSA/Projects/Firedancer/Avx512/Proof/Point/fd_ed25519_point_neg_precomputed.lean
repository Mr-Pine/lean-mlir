/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_neg_precomputed
public import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_neg
public import SSA.Projects.Firedancer.Avx512.Proof.Point.Ge.Model
public import SSA.Projects.Firedancer.Avx512.Proof.Point.Ge.Frame

/-!
# `fd_ed25519_point_neg_precomputed` conformance (AVX-512)

`negT`, a lane subtract from `2p` on the `T` lanes, stored to `r`'s first two
vectors; then `negPre`, `negT` with the `X` and `Y` lanes swapped, stored over
all three. `live?_splice2_writeQuad` drops the first two stores.
-/

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

namespace PointNegPre
open PointNeg

/-- `2p - q` on the `T` lanes (`3, 7`), `q` on the others. -/
def negT (q : Quad) : Quad where
  v03 := #v[q.v03[0], q.v03[1], q.v03[2], 17592186044378#64 - q.v03[3],
    q.v03[4], q.v03[5], q.v03[6], 17592186044414#64 - q.v03[7]]
  v14 := #v[q.v14[0], q.v14[1], q.v14[2], 17592186044414#64 - q.v14[3],
    q.v14[4], q.v14[5], q.v14[6], 17592186044414#64 - q.v14[7]]
  v25 := #v[q.v25[0], q.v25[1], q.v25[2], 17592186044414#64 - q.v25[3],
    q.v25[4], q.v25[5], q.v25[6], 2199023255550#64 - q.v25[7]]

/-- The `X` and `Y` lanes exchanged. -/
def swapXY (y : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  #v[y[1], y[0], y[2], y[3], y[5], y[4], y[6], y[7]]

/-- The result: `negT` with `X` and `Y` exchanged. -/
def negPre (q : Quad) : Quad := ⟨swapXY (negT q).v03, swapXY (negT q).v14, swapXY (negT q).v25⟩

/-- `%20`: `2p`'s limbs 0 and 3 on the `T` lanes. -/
def negTC03 : Vector (LLVM.IntW 64) 8 :=
  #v[.poison, .poison, .poison, .value 17592186044378#64,
     .poison, .poison, .poison, .value 17592186044414#64]

/-- `%29`: limbs 1 and 4. -/
def negTC14 : Vector (LLVM.IntW 64) 8 :=
  #v[.poison, .poison, .poison, .value 17592186044414#64,
     .poison, .poison, .poison, .value 17592186044414#64]

/-- `%38`: limbs 2 and 5. -/
def negTC25 : Vector (LLVM.IntW 64) 8 :=
  #v[.poison, .poison, .poison, .value 17592186044414#64,
     .poison, .poison, .poison, .value 2199023255550#64]

/-- **`%45`/`%46`, one vector's lane subtract**: `c - x` on the `T` lanes. -/
theorem denote_negTLanes {x : Vector (BitVec 64) 8} {c d : BitVec 64}
    {m t u : Vector (LLVM.IntW 64) 8}
    (hm : m = #v[.poison, .poison, .poison, .value c, .poison, .poison, .poison, .value d])
    (ht : t = Vector.ofFn fun i : Fin 8 =>
      InstCombine.binaryDenote InstCombine.MOp.BinaryOp.sub m[i.val] (x.map PoisonOr.value)[i.val])
    (hu : u = LLVM.Ty.shufflevector (e := .bitvec (.concrete 64))
      [0, 1, 2, 11, 4, 5, 6, 15] (x.map PoisonOr.value) t) :
    u = (#v[x[0], x[1], x[2], c - x[3], x[4], x[5], x[6], d - x[7]]
      : Vector (BitVec 64) 8).map PoisonOr.value := by
  subst hm ht hu
  apply Vector.ext
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i <;>
    simp [LLVM.Ty.shufflevector, InstCombine.binaryDenote, LLVM.sub, LLVM.sub?]

/-- **`%55 … %57`**: the swap, against a poison second operand it never reads. -/
theorem denote_swapXY {y : Vector (BitVec 64) 8} {w u : Vector (LLVM.IntW 64) 8}
    (hu : u = LLVM.Ty.shufflevector (e := .bitvec (.concrete 64))
      [1, 0, 2, 3, 5, 4, 6, 7] (y.map PoisonOr.value) w) :
    u = (swapXY y).map PoisonOr.value := by
  subst hu
  apply Vector.ext
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i <;> simp [LLVM.Ty.shufflevector, swapXY]

/-! ### The stores -/

/-- A store hidden by a wider one at the same offset. -/
theorem spliceBits_cover {n w w' : Nat} (bytes : BitVec n) (off : Nat) (y : BitVec w')
    (x : BitVec w) (h : w' ≤ w) :
    spliceBits (spliceBits bytes off y) off x = spliceBits bytes off x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [getLsbD_spliceBits]
  split_ifs <;> first | rfl | omega

/-- A store into `p`'s first two vectors, as one splice of `p`'s block. -/
theorem live?_splice2 {m : MemoryState} {p : Pointer} (hp : p.offset.toNat + 3 * 8 * 8 ≤ 2 ^ 64)
    (a b : Vector (BitVec 64) 8) :
    ((m.splice p (vecBV a)).splice (p.withOffset 64) (vecBV b)).live? p.id
      = (m.live? p.id).map fun blk =>
        ({ length := blk.length,
           bytes := spliceBits blk.bytes p.offsetInBits (vecBV b ++ vecBV a) } : LiveBlock) := by
  have h64 : (p.withOffset 64).offsetInBits = p.offsetInBits + 512 := by
    simp only [Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add,
      show (64 : BitVec 64).toNat = 64 from rfl]; omega
  cases hb : m.live? p.id with
  | none =>
    exact splicedDead (p := p.withOffset 64) (x := vecBV b) (splicedDead (x := vecBV a) hb)
  | some blk =>
    have e1 := splicedLive m p blk hb (vecBV a)
    have e2 := splicedLive _ (p.withOffset 64) _ e1 (vecBV b)
    simp only [Option.map_some]
    refine e2.trans ?_
    simp only [h64, spliceBits_append]

/-- The first two stores, then a `writeQuad` over them: the `writeQuad` alone. -/
theorem live?_splice2_writeQuad {m : MemoryState} {p : Pointer}
    (hp : p.offset.toNat + 3 * 8 * 8 ≤ 2 ^ 64) (a b : Vector (BitVec 64) 8) (q : Quad) :
    (((m.splice p (vecBV a)).splice (p.withOffset 64) (vecBV b)).writeQuad p q).live? p.id
      = (m.writeQuad p q).live? p.id := by
  rw [Ge.live?_writeQuad hp, Ge.live?_writeQuad hp, live?_splice2 hp]
  cases m.live? p.id with
  | none => rfl
  | some blk =>
    simp only [Option.map_some]
    congr 2
    exact spliceBits_cover _ _ _ _ (by omega)

/-! ### What the region computes -/

theorem negPre_v03 (q : Quad) : (negPre q).v03 =
    #v[q.v03[1], q.v03[0], q.v03[2], 17592186044378#64 - q.v03[3],
      q.v03[5], q.v03[4], q.v03[6], 17592186044414#64 - q.v03[7]] := rfl
theorem negPre_v14 (q : Quad) : (negPre q).v14 =
    #v[q.v14[1], q.v14[0], q.v14[2], 17592186044414#64 - q.v14[3],
      q.v14[5], q.v14[4], q.v14[6], 17592186044414#64 - q.v14[7]] := rfl
theorem negPre_v25 (q : Quad) : (negPre q).v25 =
    #v[q.v25[1], q.v25[0], q.v25[2], 17592186044414#64 - q.v25[3],
      q.v25[5], q.v25[4], q.v25[6], 2199023255550#64 - q.v25[7]] := rfl

theorem vectorFunc_negPre_X (q : Quad) : (negPre q).vectorFunc 0 = q.vectorFunc 1 := by
  funext k; fin_cases k <;> rfl

theorem vectorFunc_negPre_Y (q : Quad) : (negPre q).vectorFunc 1 = q.vectorFunc 0 := by
  funext k; fin_cases k <;> rfl

theorem vectorFunc_negPre_Z (q : Quad) : (negPre q).vectorFunc 2 = q.vectorFunc 2 := by
  funext k; fin_cases k <;> rfl

theorem vectorFunc_negPre_T (q : Quad) (hb : q.NegBounds 3) (k : Fin 6) :
    (negPre q).vectorFunc 3 k = twoPLimb k - q.vectorFunc 3 k := by
  have h := hb k
  rw [vectorFunc_eq_quadLimb] at h ⊢
  rw [vectorFunc_eq_quadLimb, negPre_v03, negPre_v14, negPre_v25]
  fin_cases k <;>
    simp only [quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat, Fin.isValue, twoPLimb,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] at h ⊢ <;>
    exact toNat_lit_sub (by norm_num) h

/-- **`negPre` is the precomputed negation.** -/
theorem ofSlots_negPre (q : Quad) (hb : q.NegBounds 3) :
    PrecomputedPoint.ofSlots (negPre q).toPoint = (PrecomputedPoint.ofSlots q.toPoint).neg := by
  show PrecomputedPoint.mk (quadElem (negPre q) 0) (quadElem (negPre q) 1)
      (quadElem (negPre q) 2) (quadElem (negPre q) 3)
    = PrecomputedPoint.mk (quadElem q 1) (quadElem q 0) (quadElem q 2) (-quadElem q 3)
  simp only [quadElem, vectorFunc_negPre_X, vectorFunc_negPre_Y, vectorFunc_negPre_Z,
    decodeNat_twoP_sub (vectorFunc_negPre_T q hb) hb]

theorem u44_negPre {q : Quad} (h03 : R43x6.U44 q.v03) (h14 : R43x6.U44 q.v14)
    (h25 : R43x6.U44 q.v25) (hb : q.NegBounds 3) :
    R43x6.U44 (negPre q).v03 ∧ R43x6.U44 (negPre q).v14 ∧ R43x6.U44 (negPre q).v25 := by
  have hl : ∀ j k, q.vectorFunc j k < 2 ^ 44 := fun j k => by
    rw [vectorFunc_eq_quadLimb]; exact quadLimb_lt q 44 (by omega) h03 h14 h25 j k
  have hT : ∀ k, twoPLimb k < 2 ^ 44 := by decide
  refine Ge.unn_of_quadLimb (by omega) fun j k => ?_
  rw [← vectorFunc_eq_quadLimb]
  fin_cases j
  · exact (vectorFunc_negPre_X q ▸ hl 1 k :)
  · exact (vectorFunc_negPre_Y q ▸ hl 0 k :)
  · exact (vectorFunc_negPre_Z q ▸ hl 2 k :)
  · show (negPre q).vectorFunc 3 k < _
    rw [vectorFunc_negPre_T q hb]; exact lt_of_le_of_lt (Nat.sub_le _ _) (hT k)

end PointNegPre

open PointNeg PointNegPre in
theorem fd_ed25519_point_neg_precomputed_conforms (r a : Pointer) (s : GlobalState)
    (hs : s.WF) (hne : r.id ≠ a.id) (hr : IsQuadPtr s.mem r) (ha : IsQuadPtr s.mem a) :
    fd_ed25519_point_neg_precomputed_spec r a s hne hr ha := by
  simp only [fd_ed25519_point_neg_precomputed_spec, Cfg.denote]
  intro hu03 hu14 hu25 hb3
  refine run_runFunction' _ ?_
  denote_step_reduce v 39 [LLVM.const?, LLVM.Ty.poison] fold

  -- `%0 … %39`: the three `2p` minuends
  replace hv20 : v20 = negTC03 := by
    simp only [hv20]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, negTC03]
  replace hv29 : v29 = negTC14 := by
    simp only [hv29]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, negTC14]
  replace hv38 : v38 = negTC25 := by
    simp only [hv38]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, negTC25]
  clear hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15 hv16 hv17
  clear hv18 hv19 hv21 hv22 hv23 hv24 hv25 hv26 hv27 hv28 hv30 hv31 hv32 hv33 hv34 hv35
  clear hv36 hv37

  -- `%40 … %44`: `a`'s three vectors, at 0, 64 and 128 bytes in
  refine Exists.elim ha.1 fun ablk ⟨hablkE, _⟩ => ?_
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

  -- `%45`, `%46`: the `03` lane subtract, stored to `r`
  denote_step_reduce v 46 only [hv20] fold
  have hN03 : v46 = (negT (readQuad ha)).v03.map PoisonOr.value :=
    denote_negTLanes rfl rfl hv46
  subst hN03
  refine name_of ({ s with mem := s.mem.splice r (vecBV (negT (readQuad ha)).v03) })
    fun s₁ hs₁ => ?_
  peel_store (negT (readQuad ha)).v03, r, hr.1, s as s₁ := hs₁
  have f₁ : Fits s₁.mem r (3 * 8 * 64) := hs₁ ▸ fits_splice hr.1

  -- `%47 … %50`: `a`'s `14` again, which the store to `r` did not reach
  have hE₁ : s₁.mem[aField.id]? = some (.live ablk) := by
    rw [hs₁]
    exact (getElem?_splice_ne (m := s.mem) (p := r) (x := vecBV (negT (readQuad ha)).v03)
      (q := aField.id) hne).trans hablkE
  peel_load (.vector 8 (.bitvec (.concrete 64))), ablk, aField, hE₁, s₁
  rw [hoffA, unflatten_readQuad_v14 ha halive]
  denote_step_reduce v 49 only [hv29] fold
  have hN14 : v49 = (negT (readQuad ha)).v14.map PoisonOr.value :=
    denote_negTLanes rfl rfl hv49
  subst hN14
  peel_gep 64 with r, f₁, s₁ as rField
  have fR : Fits s₁.mem rField 1024 := Fits.mono hrField (by simp)
  refine name_of
    ({ s₁ with mem := s₁.mem.splice rField (vecBV (negT (readQuad ha)).v14) })
    fun s₂ hs₂ => ?_
  peel_store (negT (readQuad ha)).v14, rField, fR, s₁ as s₂ := hs₂
  have f₂ : Fits s₂.mem r (3 * 8 * 64) := hs₂ ▸ fits_splice f₁

  -- `%51 … %54`: the same for `25`, not stored yet
  have hE₂ : s₂.mem[aField25.id]? = some (.live ablk) := by
    rw [hs₂]
    exact (getElem?_splice_ne (m := s₁.mem) (p := rField)
      (x := vecBV (negT (readQuad ha)).v14) (q := aField25.id) hne).trans hE₁
  peel_load (.vector 8 (.bitvec (.concrete 64))), ablk, aField25, hE₂, s₂
  rw [hoffA25, unflatten_readQuad_v25 ha halive]
  denote_step_reduce v 53 only [hv38] fold
  have hN25 : v53 = (negT (readQuad ha)).v25.map PoisonOr.value :=
    denote_negTLanes rfl rfl hv53
  subst hN25
  peel_gep 128 with r, f₂, s₂ as rField25
  have fR25 : Fits s₂.mem rField25 512 := Fits.mono hrField25 (by simp)

  -- `%55 … %57`: `X` and `Y` swapped, one store per vector
  denote_step_reduce v 55 only [hv39] fold
  have hS03 : v55 = (negPre (readQuad ha)).v03.map PoisonOr.value := denote_swapXY hv55
  subst hS03
  refine name_of
    ({ s₂ with mem := s₂.mem.splice r (vecBV (negPre (readQuad ha)).v03) })
    fun s₃ hs₃ => ?_
  peel_store (negPre (readQuad ha)).v03, r, f₂, s₂ as s₃ := hs₃

  denote_step_reduce v 56 only [hv39] fold
  have hS14 : v56 = (negPre (readQuad ha)).v14.map PoisonOr.value := denote_swapXY hv56
  subst hS14
  have f₄ : Fits s₃.mem rField (8 * 64) := by
    rw [hs₃, hs₂]; exact fits_splice (fits_splice (Fits.mono fR (by omega)))
  refine name_of
    ({ s₃ with mem := s₃.mem.splice rField (vecBV (negPre (readQuad ha)).v14) })
    fun s₄ hs₄ => ?_
  peel_store (negPre (readQuad ha)).v14, rField, f₄, s₃ as s₄ := hs₄

  denote_step_reduce v 57 only [hv39] fold
  have hS25 : v57 = (negPre (readQuad ha)).v25.map PoisonOr.value := denote_swapXY hv57
  subst hS25
  have f₅ : Fits s₄.mem rField25 (8 * 64) := by
    rw [hs₄, hs₃]; exact fits_splice (fits_splice fR25)
  refine name_of
    ({ s₄ with mem := s₄.mem.splice rField25 (vecBV (negPre (readQuad ha)).v25) })
    fun s₅ hs₅ => ?_
  peel_store (negPre (readQuad ha)).v25, rField25, f₅, s₄ as s₅ := hs₅

  -- `return %arg0`, in `s₅`
  refine ⟨s₅, by simp_return, negPre (readQuad ha), ?_, ofSlots_negPre _ hb3,
    u44_negPre hu03 hu14 hu25 hb3⟩

  /- The region has returned: its stores are one `writeQuad`. -/
  have hmem : s₅.mem = ((s.mem.splice r (vecBV (negT (readQuad ha)).v03)).splice
      (r.withOffset 64) (vecBV (negT (readQuad ha)).v14)).writeQuad r (negPre (readQuad ha)) := by
    rw [hs₅, hs₄, hs₃, hs₂, hs₁]; unfold MemoryState.writeQuad; dsimp only
  rw [hmem]
  refine GlobalState.Equiv.symm (popFrame_equiv_block hs (lt_nextFreeBlock_of_fits hs hr.1)
    (fun b _ hne' => ?_) (fun _ hne' => Ge.live?_writeQuad_ne (Ne.symm hne'))
    (live?_splice2_writeQuad hr.2 _ _ _))
  have h := Ne.symm hne'
  rw [Ge.live?_writeQuad_ne h, live?_splice_ne (p := r.withOffset 64) h, live?_splice_ne (p := r) h]

end Firedancer.Avx512

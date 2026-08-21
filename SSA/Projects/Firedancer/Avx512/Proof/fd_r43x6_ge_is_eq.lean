/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.fd_r43x6_ge_is_eq
import SSA.Projects.Firedancer.Avx512.Proof.fd_r43x6_quad_mul_fast
import SSA.Projects.Firedancer.Avx512.Proof.fd_r43x6_is_nonzero
import SSA.Projects.Firedancer.Avx512.Spec.fd_r43x6_ge_is_eq
import SSA.Projects.Firedancer.Curve

/-!
# `fd_r43x6_ge_is_eq` decides point equality

The obligations of `Spec/fd_r43x6_ge_is_eq.lean`, discharged, and the lifted
region derived against the model. Two layers:

* **The model decides equality** (`geIsEqDecides`): `GeIsEqDecides`, from
  `samePoint_iff_cross_sub_eq_zero` composed with `IsNonzeroDecides` through
  the spec's decode lemmas. This is arithmetic only -- no denotation.

* **The region computes the model** (`run_fd_r43x6_ge_is_eq`): the
  instruction-by-instruction derivation. Unlike every earlier derivation this
  one runs against a concrete state throughout -- the memory operations sit in
  the *middle* of the program (allocas, then the `fd_r43x6_quad_mul_fast`
  call, then the loads back), so the loaded values exist only once a state is
  threaded through. `denote_step_all` steps the pure instructions under the
  `.run s` wrapper; each impure instruction is peeled with the run-form step
  lemmas of `SLLVM/Dialect/Semantics/StepLemmas.lean`; the two callees are
  never re-derived -- `denote_fd_r43x6_quad_mul_fast` and
  `spec_denote_fd_r43x6_is_nonzero` are single rewrites.

The permutes are handled at the element level: `shufP`/`shufQ` are the two
`FD_R43X6_QUAD_PERMUTE` masks as vector maps, and `quadMulLimb_shuf` says the
quad multiply on the permuted QUADs computes exactly the spec's four cross
products.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-! ## The two permutes, and what the multiply makes of them -/

/-- `FD_R43X6_QUAD_PERMUTE(X, 2,0,2,1)`, at the QUAD level: the QUAD holding the
coordinates `(Z, X, Z, Y)` of the point `X` holds. -/
def shufP (x : Quad) : Quad :=
  encodeQuad x.PointVecs.Z x.PointVecs.X x.PointVecs.Z x.PointVecs.Y

/-- `FD_R43X6_QUAD_PERMUTE(Y, 0,2,1,2)`: `(X, Z, Y, Z)`. -/
def shufQ (y : Quad) : Quad :=
  encodeQuad y.PointVecs.X y.PointVecs.Z y.PointVecs.Y y.PointVecs.Z

/-- Looking one of three freshly inserted blocks back up. -/
private theorem frame_lookup (m : Std.HashMap BlockId Block) (n : ℕ) (B : Block) :
    ((((m.insert ⟨n⟩ B).insert ⟨n + 1⟩ B).insert ⟨n + 1 + 1⟩ B)[(⟨n⟩ : BlockId)]?
        = some B)
    ∧ ((((m.insert ⟨n⟩ B).insert ⟨n + 1⟩ B).insert ⟨n + 1 + 1⟩ B)[(⟨n + 1⟩ : BlockId)]?
        = some B)
    ∧ ((((m.insert ⟨n⟩ B).insert ⟨n + 1⟩ B).insert ⟨n + 1 + 1⟩ B)[(⟨n + 1 + 1⟩ : BlockId)]?
        = some B) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Std.HashMap.getElem?_insert,
      if_neg (by simp only [beq_iff_eq, BlockId.mk.injEq]; omega),
      Std.HashMap.getElem?_insert,
      if_neg (by simp only [beq_iff_eq, BlockId.mk.injEq]; omega),
      Std.HashMap.getElem?_insert_self]
  · rw [Std.HashMap.getElem?_insert,
      if_neg (by simp only [beq_iff_eq, BlockId.mk.injEq]; omega),
      Std.HashMap.getElem?_insert_self]
  · rw [Std.HashMap.getElem?_insert_self]

/-! ### The derivation itself -/

local macro "ge_op " h:term " with " hs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| (simp only [$h:term, Expr.denoteOp1, Expr.denoteOpPure]
             simp_peephole
             simp +zetaDelta [HVector.head, $hs,*]))

/-- As `denote_shuffle`/`denote_vecbin`, for a `vpermi2var`. -/
local macro "ge_permi " h:term " with " hs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| (simp only [$h:term, Expr.denoteOp1, Expr.denoteOpPure]
             simp_peephole
             simp only [HVector.head]
             apply Vector.ext
             intro i hi
             interval_cases i
             all_goals simp +zetaDelta
               [LLVM.Ty.vpermi2var, LLVM.Ty.vpermi2varLane, toBitVecValue,
                Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_mk,
                List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
                $hs,*]))

def quadDualValuation (x y: Quad) :
    Ctxt.Valuation (Ctxt.ofList [QTy, QTy, QTy, QTy, QTy, QTy]) :=
  y.v25.map PoisonOr.value ::ᵥ y.v14.map PoisonOr.value ::ᵥ y.v03.map PoisonOr.value ::ᵥ
  x.v25.map PoisonOr.value ::ᵥ x.v14.map PoisonOr.value ::ᵥ x.v03.map PoisonOr.value ::ᵥ
    Ctxt.Valuation.nil

/-- `u46 ⊆ u47`: the permuted QUADs are `u46`, the multiply kernel is stated at
its own `u47`. -/
private theorem unn_mono {x : Vector (BitVec 64) 8} {m n : ℕ} (hmn : m ≤ n)
    (hx : R43x6.UNN m x) : R43x6.UNN n x := by
  refine ⟨fun i => le_trans (hx.1 i) ?_, hx.2⟩
  have h : ((2 : ℤ) ^ m) ≤ (2 : ℤ) ^ n := by
    exact_mod_cast Nat.pow_le_pow_right (by omega) hmn
  omega

/-- A vector whose lanes are all lanes of a `UNN n` vector is itself `UNN n`:
a permute, or the re-encoding of a point into a QUAD, only moves limbs around.
`σ` says which lane of `v` each lane of `w` is. -/
private theorem unn_of_lanes {n : ℕ} {v w : Vector (BitVec 64) 8} (hv : R43x6.UNN n v)
    (σ : Vector (Fin 8) 8) (h : ∀ i : Fin 8, w[i] = v[σ[i]]) : R43x6.UNN n w := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · show (w[(i : ℕ)]'i.isLt).toInt ≤ 2 ^ n - 1
    rw [show (w[(i : ℕ)]'i.isLt) = v[(σ[i] : ℕ)]'(σ[i]).isLt from h i]
    exact hv.1 σ[i]
  · show 0 ≤ (w[(i : ℕ)]'i.isLt).toInt
    rw [show (w[(i : ℕ)]'i.isLt) = v[(σ[i] : ℕ)]'(σ[i]).isLt from h i]
    exact hv.2 σ[i]


/-- `load` reads only the block at `p.id`: a memory agreeing with `m` there loads
the same value, and is left alone as `m` is. -/
private theorem run_load_congr {t : LLVM.Ty} {m m' : MemoryState} {p : Pointer}
    {x : TyDenote.toType t} (hm : m'[p.id]? = m[p.id]?)
    (h : (SLLVM.load (.value p) t).run m = .value (x, m)) :
    (SLLVM.load (.value p) t).run m' = .value (x, m') := by
  rcases hb : m[p.id]? with _ | ⟨_ | blk⟩
  · simp [SLLVM.load, SLLVM.getLiveBlockOrUB, hb, PoisonOr.getOrUB, PoisonOr.poison_ne_value] at h
  · simp [SLLVM.load, SLLVM.getLiveBlockOrUB, hb, PoisonOr.getOrUB, PoisonOr.poison_ne_value] at h
  · by_cases hlen : p.offsetInBits + LLVM.Ty.width t ≤ blk.lengthInBits
    · rw [SLLVM.run_load hb hlen] at h
      rw [SLLVM.run_load (hm.trans hb) hlen]
      simp only [PoisonOr.value_inj, Prod.mk.injEq, and_true] at h ⊢
      exact h
    · simp [SLLVM.load, SLLVM.getLiveBlockOrUB, hb, PoisonOr.getOrUB, throwUBIf,
        Nat.not_le.mp hlen, PoisonOr.poison_ne_value] at h

/-- **Readback through the frame kill.** After the callee's three stores and
the deallocation of its frame, each destination -- allocated *before* the
call's counter snapshot -- still addresses the vector stored through it:
`storeVec3_readback`, through `killFrom`, which leaves blocks below the
counter alone. -/
private theorem killFrom_readback {q₀ q₁ q₂ : Pointer} {u v w : Vector (BitVec 64) 8}
    {m : MemoryState} {n₀ : ℕ}
    (h₀ : Fits m q₀ 512) (h₁ : Fits m q₁ 512) (h₂ : Fits m q₂ 512)
    (d₀₁ : q₀.id ≠ q₁.id) (d₀₂ : q₀.id ≠ q₂.id) (d₁₂ : q₁.id ≠ q₂.id)
    (l₀ : q₀.id.id < n₀) (l₁ : q₁.id.id < n₀) (l₂ : q₂.id.id < n₀) :
    let m' := MemoryState.killFrom n₀ (((m.writeVec q₀ u).writeVec q₁ v).writeVec q₂ w)
    (SLLVM.load (.value q₀) QVecTy).run m' = .value (u.map PoisonOr.value, m')
      ∧ (SLLVM.load (.value q₁) QVecTy).run m' = .value (v.map PoisonOr.value, m')
      ∧ (SLLVM.load (.value q₂) QVecTy).run m' = .value (w.map PoisonOr.value, m') := by
  obtain ⟨r₀, r₁, r₂⟩ := storeVec3_readback (u := u) (v := v) (w := w) h₀ h₁ h₂ d₀₁ d₀₂ d₁₂
  exact ⟨run_load_congr (SLLVM.getElem?_killFrom_of_lt l₀) r₀,
    run_load_congr (SLLVM.getElem?_killFrom_of_lt l₁) r₁,
    run_load_congr (SLLVM.getElem?_killFrom_of_lt l₂) r₂⟩

/-! ### The difference vector -/

/-- The vector `fd_r43x6_sub_fast` leaves for `fd_r43x6_is_nonzero`: the six
difference limbs of `subFast`, lanes 6 and 7 zero. -/
def subFastVec (x y : Fin 6 → ℕ) : Vector (BitVec 64) 8 :=
  #v[BitVec.ofInt 64 (subFast x y 0), BitVec.ofInt 64 (subFast x y 1),
     BitVec.ofInt 64 (subFast x y 2), BitVec.ofInt 64 (subFast x y 3),
     BitVec.ofInt 64 (subFast x y 4), BitVec.ofInt 64 (subFast x y 5), 0, 0]

/-- One lane of the compiled `sub`-then-`add`: the wrap-around arithmetic on
64-bit lanes computes exactly the `ℤ`-level limb, encoded by `ofInt`. -/
private theorem sub_add_lane (x y : ℕ) (c : ℤ) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 y + BitVec.ofInt 64 c
      = BitVec.ofInt 64 ((x : ℤ) - (y : ℤ) + c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

/-- The lanes read back as the `ℤ` limbs, given the `s62` range. -/
private theorem extractLimbs_subFastVec {x y : Fin 6 → ℕ}
    (hx : ∀ k, x k < 7000 * 2 ^ 49) (hy : ∀ k, y k < 7000 * 2 ^ 49) :
    R43x6.extractLimbs (subFastVec x y) = subFast x y := by
  have hs := subFast_s62 hx hy
  funext i
  have hi := hs i
  have : R43x6.FitsLong (subFast x y i) := by
    simp only [R43x6.FitsLong]; omega
  fin_cases i <;>
    simpa [R43x6.extractLimbs, LimbRepresentations.toInts, subFastVec] using
      toInt_ofInt this

/-- The difference vector is `s62`, as the C comments claim. -/
private theorem s62_subFastVec {x y : Fin 6 → ℕ}
    (hx : ∀ k, x k < 7000 * 2 ^ 49) (hy : ∀ k, y k < 7000 * 2 ^ 49) :
    R43x6.S62 ((subFastVec x y).take R43x6.limbCount) := by
  have hs := subFast_s62 hx hy
  have key : ∀ i : Fin R43x6.limbCount,
      LimbRepresentations.toInts ((subFastVec x y).take R43x6.limbCount) i
        = subFast x y i := by
    intro i
    rw [R43x6.toInts_take, ← extractLimbs_subFastVec hx hy]
  constructor <;> intro i <;> rw [key i] <;> exact (by have := hs i; omega)

/-- `quadLimb` of an encoded QUAD is the lane function of the element encoded. -/
private theorem quadLimb_encodeQuad (a b c d : Vector (BitVec 64) 6) :
    quadLimb (encodeQuad a b c d).v03 (encodeQuad a b c d).v14 (encodeQuad a b c d).v25 0 = laneFunc a
  ∧ quadLimb (encodeQuad a b c d).v03 (encodeQuad a b c d).v14 (encodeQuad a b c d).v25 1 = laneFunc b
  ∧ quadLimb (encodeQuad a b c d).v03 (encodeQuad a b c d).v14 (encodeQuad a b c d).v25 2 = laneFunc c
  ∧ quadLimb (encodeQuad a b c d).v03 (encodeQuad a b c d).v14 (encodeQuad a b c d).v25 3 = laneFunc d := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext i <;> fin_cases i <;> rfl

/-- **The multiply on the permuted QUADs is the four cross products**, lane for
lane: `(xn2, xn1, yn2, yn1)`, exactly the spec's limb functions. -/
private theorem quadMulLimb_shuf (x y : Quad) :
    quadMulLimb (shufP x) (shufQ y) 0 = xn2Limb x y
  ∧ quadMulLimb (shufP x) (shufQ y) 1 = xn1Limb x y
  ∧ quadMulLimb (shufP x) (shufQ y) 2 = yn2Limb x y
  ∧ quadMulLimb (shufP x) (shufQ y) 3 = yn1Limb x y := by
  obtain ⟨hp0, hp1, hp2, hp3⟩ :=
    quadLimb_encodeQuad x.PointVecs.Z x.PointVecs.X x.PointVecs.Z x.PointVecs.Y
  obtain ⟨hq0, hq1, hq2, hq3⟩ :=
    quadLimb_encodeQuad y.PointVecs.X y.PointVecs.Z y.PointVecs.Y y.PointVecs.Z
  simp only [shufP, shufQ]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext k
  · show limb (quadLimb _ _ _ 0) (quadLimb _ _ _ 0) k = _
    rw [hp0, hq0]; rfl
  · show limb (quadLimb _ _ _ 1) (quadLimb _ _ _ 1) k = _
    rw [hp1, hq1]; rfl
  · show limb (quadLimb _ _ _ 2) (quadLimb _ _ _ 2) k = _
    rw [hp2, hq2]; rfl
  · show limb (quadLimb _ _ _ 3) (quadLimb _ _ _ 3) k = _
    rw [hp3, hq3]; rfl

set_option maxHeartbeats 4000000 in
/-- **Denotation of `fd_r43x6_ge_is_eq`**: on two `u46` QUADs the function
returns the model's answer and leaves the stack as it found it -- its three
slots are its frame, popped by `runFunction`. The callees are single rewrites:
`denote_fd_r43x6_quad_mul_fast` at the call, and
`spec_denote_fd_r43x6_is_nonzero` at the two `fd_r43x6_is_nonzero` calls. -/
theorem run_fd_r43x6_ge_is_eq (x y : Quad)
    (hx03 : R43x6.U46 x.v03) (hx14 : R43x6.U46 x.v14) (hx25 : R43x6.U46 x.v25)
    (hy03 : R43x6.U46 y.v03) (hy14 : R43x6.U46 y.v14) (hy25 : R43x6.U46 y.v25)
    (s : GlobalState) (hs : s.WF) :
    ∃ s', StateT.run (runFunction (fd_r43x6_ge_is_eq.denote (quadDualValuation x y))) s
        = .value ([PoisonOr.value (geIsEq x y)]ₕ, s')
      ∧ s' ≈ s := by
  -- The body: three slots at the entry counter, nothing below it changed --
  -- all `runFunction` needs to pop the frame.
  suffices body : ∃ m, StateT.run (fd_r43x6_ge_is_eq.denote (quadDualValuation x y)) s
      = .value ([PoisonOr.value (geIsEq x y)]ₕ, ⟨⟨s.alloc.nextFreeBlock + 3⟩, m⟩)
      ∧ ∀ q : BlockId, q.id < s.alloc.nextFreeBlock → m.live? q = s.mem.live? q by
    obtain ⟨m, h, hm⟩ := body
    exact ⟨_, run_runFunction h, GlobalState.killFrom_equiv m hs hm⟩

  let X := x.PointVecs
  let Y := y.PointVecs
  -- the permuted QUADs, as the encodings of the reordered coordinate vectors:
  -- `(2,0,2,1)` puts `(Z, X, Z, Y)` in the four slots, `(0,2,1,2)` puts `(X, Z, Y, Z)`
  let XShuff := encodeQuad X.Z X.X X.Z X.Y
  let XShuff03 := XShuff.v03.map PoisonOr.value
  let XShuff14 := XShuff.v14.map PoisonOr.value
  let XShuff25 := XShuff.v25.map PoisonOr.value
  let YShuff := encodeQuad Y.X Y.Z Y.Y Y.Z
  let YShuff03 := YShuff.v03.map PoisonOr.value
  let YShuff14 := YShuff.v14.map PoisonOr.value
  let YShuff25 := YShuff.v25.map PoisonOr.value
  let resultQuad : Quad := quadMulResult XShuff YShuff

  -- the frame: three slots at the entry counter, holding the cross products
  let mem_slot_1 := s.alloc.nextFreeBlock
  let mem_slot_2 := mem_slot_1 + 1
  let mem_slot_3 := mem_slot_2 + 1
  obtain ⟨MAlloc, hMAlloc⟩ : ∃ MAlloc, MAlloc =
    (⟨((s.mem.mem.insert ⟨mem_slot_1⟩
          (.live { length := (512 + 7) / 8, bytes := 0#_ })).insert
          ⟨mem_slot_2⟩
          (.live { length := (512 + 7) / 8, bytes := 0#_ })).insert
          ⟨mem_slot_3⟩
          (.live { length := (512 + 7) / 8, bytes := 0#_ })⟩ : MemoryState) :=
  ⟨_, rfl⟩
  refine ⟨MemoryState.killFrom (mem_slot_3 + 1)
    (((MAlloc.writeVec ⟨⟨mem_slot_1⟩, 0⟩ resultQuad.v03).writeVec
      ⟨⟨mem_slot_2⟩, 0⟩ resultQuad.v14).writeVec ⟨⟨mem_slot_3⟩, 0⟩ resultQuad.v25), ?_, ?frame⟩
  -- below the counter, neither the kill nor the stores nor the allocas touch a block
  case frame =>
    intro q hq
    have h1 : (⟨mem_slot_1⟩ : BlockId) ≠ q := by
      rintro rfl; change s.alloc.nextFreeBlock < s.alloc.nextFreeBlock at hq; omega
    have h2 : (⟨mem_slot_2⟩ : BlockId) ≠ q := by
      rintro rfl; change s.alloc.nextFreeBlock + 1 < s.alloc.nextFreeBlock at hq; omega
    have h3 : (⟨mem_slot_3⟩ : BlockId) ≠ q := by
      rintro rfl; change s.alloc.nextFreeBlock + 1 + 1 < s.alloc.nextFreeBlock at hq; omega
    rw [live?_killFrom_of_lt (by simp only [mem_slot_3, mem_slot_2]; omega)]
    simp only [MemoryState.live?, MemoryState.writeVec,
      getElem?_splice_ne (p := ⟨⟨mem_slot_1⟩, 0⟩) h1, getElem?_splice_ne (p := ⟨⟨mem_slot_2⟩, 0⟩) h2,
      getElem?_splice_ne (p := ⟨⟨mem_slot_3⟩, 0⟩) h3, hMAlloc, MemoryState.getElem?_eq,
      Std.HashMap.getElem?_insert, beq_iff_eq, h1, h2, h3, if_false]

  simp only [fd_r43x6_ge_is_eq]
  let zero32: LLVM.IntW _ := .value 0#32
  let zero: LLVM.IntW _ := .value 0#64
  let one: LLVM.IntW _ := .value 1#32
  denote_step_all v 3

  have v0Value : v0 = one := by
    ge_op hv0 with LLVM.const?
  have v3Value : v3 = zero := by
    ge_op hv3 with LLVM.const?
  let poisonVec : Vector (LLVM.IntW 64) 8 := (Vector.replicate 8 .poison)
  have v1Value : v1 = poisonVec := by
    ge_op hv1 with LLVM.Ty.poison
  have v2Value : v2 = .poison := by ge_op hv2 with LLVM.Ty.poison
  subst v0Value v1Value v2Value v3Value
  denote_clear v 0 3

  denote_step_all v 20
  let zeroEven : Vector (LLVM.IntW 64) 8 := #v[.value 0#64, .poison, .value 0#64, .poison, .value 0#64, .poison, .value 0#64, .poison]
  have v20Value : v20 = zeroEven := by
    denote_eval v 4 20
    denote_expand v 4 20
    simp [LLVM.Ty.insertelement, LLVM.Ty.poison, LLVM.const?]
    rfl
  subst v20Value
  denote_clear v 4 20

  denote_step_all v 37
  let zeroOdd : Vector (LLVM.IntW 64) 8 := #v[.poison, .value 0#64, .poison, .value 0#64, .poison, .value 0#64, .poison, .value 0#64]
  have v37Value : v37 = zeroOdd := by
    denote_eval v 21 37
    denote_expand v 21 37
    simp [LLVM.Ty.insertelement, LLVM.Ty.poison, LLVM.const?]
    rfl
  subst v37Value
  denote_clear v 21 37

  denote_step_all v 40
  let unpackIdxs1 : Vector (LLVM.IntW 64) 8 := #v[.value 0#64, .value 1#64, .value 8#64, .value 4#64, .value 5#64, .value 12#64, .value 9#64, .value 9#64]
  let unpackIdxs2 : Vector (LLVM.IntW 64) 8 := #v[.value 2#64, .value 3#64, .value 10#64, .value 6#64, .value 7#64, .value 14#64, .value 9#64, .value 9#64]
  let pVec : Vector (BitVec 64) 8 := #v[8796093022189#64, 8796093022207#64, 8796093022207#64, 8796093022207#64, 8796093022207#64, 1099511627775#64, 0#64, 0#64]
  let pVec' : Vector (LLVM.IntW 64) 8 := pVec.map PoisonOr.value

  have v38Value : v38 = unpackIdxs1 := by denote_dense hv38
  have v39Value : v39 = unpackIdxs2 := by denote_dense hv39
  have v40Value : v40 = pVec' := by denote_dense hv40
  subst v38Value v39Value v40Value
  denote_clear v 38 40

  denote_step_all v 41
  let neg1: LLVM.IntW _ := .value (-1#32)
  have v41Value : v41 = neg1 := by ge_op hv41 with LLVM.const?
  subst v41Value
  denote_clear v 41 41

  -- Alloca three vectors
  rw [SLLVM.run_var_alloca, SLLVM.run_var_alloca, SLLVM.run_var_alloca]
  dsimp only
  rw [← hMAlloc]

  denote_step_all v 50

  -- the permutes only move limbs of `x` / `y` around, so the permuted QUADs
  -- stay `u46`: lane `i` of `XShuff.v03` is lane `(2,0,2,1,6,4,6,5)[i]` of
  -- `x.v03`, likewise for the other thirds; `(0,2,1,2,4,6,5,6)` for `y`
  have hXShuff03 : R43x6.U46 XShuff.v03 :=
    unn_of_lanes hx03 #v[2, 0, 2, 1, 6, 4, 6, 5] (by intro i; fin_cases i <;> rfl)
  have hXShuff14 : R43x6.U46 XShuff.v14 :=
    unn_of_lanes hx14 #v[2, 0, 2, 1, 6, 4, 6, 5] (by intro i; fin_cases i <;> rfl)
  have hXShuff25 : R43x6.U46 XShuff.v25 :=
    unn_of_lanes hx25 #v[2, 0, 2, 1, 6, 4, 6, 5] (by intro i; fin_cases i <;> rfl)
  have hYShuff03 : R43x6.U46 YShuff.v03 :=
    unn_of_lanes hy03 #v[0, 2, 1, 2, 4, 6, 5, 6] (by intro i; fin_cases i <;> rfl)
  have hYShuff14 : R43x6.U46 YShuff.v14 :=
    unn_of_lanes hy14 #v[0, 2, 1, 2, 4, 6, 5, 6] (by intro i; fin_cases i <;> rfl)
  have hYShuff25 : R43x6.U46 YShuff.v25 :=
    unn_of_lanes hy25 #v[0, 2, 1, 2, 4, 6, 5, 6] (by intro i; fin_cases i <;> rfl)
  -- and at `u47`, the width `denote_fd_r43x6_quad_mul_fast` is stated at
  have hXShuff03' : R43x6.U47 XShuff.v03 := unn_mono (by omega) hXShuff03
  have hXShuff14' : R43x6.U47 XShuff.v14 := unn_mono (by omega) hXShuff14
  have hXShuff25' : R43x6.U47 XShuff.v25 := unn_mono (by omega) hXShuff25
  have hYShuff03' : R43x6.U47 YShuff.v03 := unn_mono (by omega) hYShuff03
  have hYShuff14' : R43x6.U47 YShuff.v14 := unn_mono (by omega) hYShuff14
  have hYShuff25' : R43x6.U47 YShuff.v25 := unn_mono (by omega) hYShuff25

  have v45Value : v45 = XShuff03 := by denote_shuffle hv45 with quadDualValuation, Quad.PointVecs, Quad.vector, quadElemVec, encodeQuad, Vector.getElem_map
  have v46Value : v46 = XShuff14 := by denote_shuffle hv46 with quadDualValuation, Quad.PointVecs, Quad.vector, quadElemVec, encodeQuad, Vector.getElem_map
  have v47Value : v47 = XShuff25 := by denote_shuffle hv47 with quadDualValuation, Quad.PointVecs, Quad.vector, quadElemVec, encodeQuad, Vector.getElem_map
  have v48Value : v48 = YShuff03 := by denote_shuffle hv48 with quadDualValuation, Quad.PointVecs, Quad.vector, quadElemVec, encodeQuad, Vector.getElem_map
  have v49Value : v49 = YShuff14 := by denote_shuffle hv49 with quadDualValuation, Quad.PointVecs, Quad.vector, quadElemVec, encodeQuad, Vector.getElem_map
  have v50Value : v50 = YShuff25 := by denote_shuffle hv50 with quadDualValuation, Quad.PointVecs, Quad.vector, quadElemVec, encodeQuad, Vector.getElem_map
  subst v45Value v46Value v47Value v48Value v49Value v50Value
  denote_clear v 45 50

  rw [SLLVM.run_var_lifetime, SLLVM.run_var_lifetime, SLLVM.run_var_lifetime]

  let state_after: GlobalState := {
    alloc := ⟨mem_slot_3 + 1⟩,
    mem := MemoryState.killFrom (mem_slot_3 + 1) (
      let with_val_1 := MAlloc.writeVec ⟨⟨mem_slot_1⟩, 0⟩ resultQuad.v03
      let with_val_2 := with_val_1.writeVec ⟨⟨mem_slot_2⟩, 0⟩ resultQuad.v14
      let with_val_3 := with_val_2.writeVec ⟨⟨mem_slot_3⟩, 0⟩ resultQuad.v25
      with_val_3
    )
  }

  -- the three slots of `MAlloc` are live and big enough
  have hfits := frame_lookup s.mem.mem mem_slot_1 (.live { length := (512 + 7) / 8, bytes := 0#_ })
  have hfit0 : Fits MAlloc ⟨⟨mem_slot_1⟩, 0⟩ 512 :=
    hMAlloc ▸ ⟨_, hfits.1, by simp [LiveBlock.lengthInBits, Pointer.offsetInBits]⟩
  have hfit1 : Fits MAlloc ⟨⟨mem_slot_2⟩, 0⟩ 512 :=
    hMAlloc ▸ ⟨_, hfits.2.1, by simp [LiveBlock.lengthInBits, Pointer.offsetInBits]⟩
  have hfit2 : Fits MAlloc ⟨⟨mem_slot_3⟩, 0⟩ 512 :=
    hMAlloc ▸ ⟨_, hfits.2.2, by simp [LiveBlock.lengthInBits, Pointer.offsetInBits]⟩
  -- and still after the callee's first one and two stores (`run_storeVec3` threads them)
  have hfit1' : Fits (MAlloc.writeVec ⟨⟨mem_slot_1⟩, 0⟩ resultQuad.v03) ⟨⟨mem_slot_2⟩, 0⟩ 512 := by
    rw [MemoryState.writeVec]; exact fits_splice hfit1
  have hfit2' : Fits ((MAlloc.writeVec ⟨⟨mem_slot_1⟩, 0⟩ resultQuad.v03).writeVec
      ⟨⟨mem_slot_2⟩, 0⟩ resultQuad.v14) ⟨⟨mem_slot_3⟩, 0⟩ 512 := by
    rw [MemoryState.writeVec, MemoryState.writeVec]; exact fits_splice (fits_splice hfit2)

  refine (SLLVM.run_denote_var_zero (s' := state_after) ?_).trans ?_
  · rw [SLLVM.denoteOp_call_impure]
    change StateT.run (SLLVM.runFunction (fd_r43x6_quad_mul_fast.denote (quadDualValMem
          (.value ⟨⟨mem_slot_1⟩, 0⟩) (.value ⟨⟨mem_slot_2⟩, 0⟩) (.value ⟨⟨mem_slot_3⟩, 0⟩)
          XShuff YShuff))) _ = _
    rw [denote_fd_r43x6_quad_mul_fast XShuff YShuff hXShuff03' hXShuff14' hXShuff25' hYShuff03' hYShuff14' hYShuff25']
    have h3 := run_storeVec3 (u := (quadMulResult XShuff YShuff).v03)
      (v := (quadMulResult XShuff YShuff).v14) (w := (quadMulResult XShuff YShuff).v25)
      (s := { alloc := ⟨s.alloc.nextFreeBlock + 1 + 1 + 1⟩, mem := MAlloc }) hfit0 hfit1' hfit2'
    -- peel `getThe`, evaluate the three stores with `h3`, peel the frame kill,
    -- the counter restore and `pure`; what is left is `state_after` up to its `let`s
    simp only [SLLVM.runFunction, EffectM.run_bind, SLLVM.run_getThe_alloc, PoisonOr.value_bind,
      SLLVM.run_modifyThe_mem, SLLVM.run_modifyThe_alloc, EffectM.run_pure]
    simp only [EffectM.run_bind, EffectM.run_pure] at h3
    simp only [h3, PoisonOr.value_bind]
    rfl
  ·
    have hd01 : (⟨⟨mem_slot_1⟩, 0⟩ : Pointer).id ≠ (⟨⟨mem_slot_2⟩, 0⟩ : Pointer).id := by
      simp only [ne_eq, BlockId.mk.injEq, mem_slot_2]; omega
    have hd02 : (⟨⟨mem_slot_1⟩, 0⟩ : Pointer).id ≠ (⟨⟨mem_slot_3⟩, 0⟩ : Pointer).id := by
      simp only [ne_eq, BlockId.mk.injEq, mem_slot_3, mem_slot_2]; omega
    have hd12 : (⟨⟨mem_slot_2⟩, 0⟩ : Pointer).id ≠ (⟨⟨mem_slot_3⟩, 0⟩ : Pointer).id := by
      simp only [ne_eq, BlockId.mk.injEq, mem_slot_3]; omega
    obtain ⟨hld0, hld1, hld2⟩ :=
      killFrom_readback (n₀ := mem_slot_3 + 1)
        (u := (quadMulResult XShuff YShuff).v03) (v := (quadMulResult XShuff YShuff).v14)
        (w := (quadMulResult XShuff YShuff).v25)
        hfit0 hfit1 hfit2 hd01 hd02 hd12
        (by simp only [mem_slot_3, mem_slot_2]; omega)
        (by simp only [mem_slot_3, mem_slot_2]; omega)
        (by simp only [mem_slot_3]; omega)
    rw [SLLVM.run_var_load hld0, SLLVM.run_var_load hld1, SLLVM.run_var_load hld2]
    rw [SLLVM.run_var_lifetime, SLLVM.run_var_lifetime, SLLVM.run_var_lifetime]
    clear hd01 hd02 hd12 hfit0 hfits hfit1 hfit2 hfit1' hfit2'

    denote_step_all v 61
    let xn2 := resultQuad.vector 0
    let xn1 := resultQuad.vector 1
    let yn2 := resultQuad.vector 2
    let yn1 := resultQuad.vector 3
    -- `'(by decide)`: the default `get_elem_tactic` times out in this context
    let tmp_c0 := #v[xn2[0]'(by decide), xn2[1]'(by decide), yn2[0]'(by decide), yn2[1]'(by decide),
      xn2[3]'(by decide), xn2[4]'(by decide), yn2[3]'(by decide), yn2[4]'(by decide)]
    let tmp_c1 := #v[xn1[0]'(by decide), xn1[1]'(by decide), yn1[0]'(by decide), yn1[1]'(by decide),
      xn1[3]'(by decide), xn1[4]'(by decide), yn1[3]'(by decide), yn1[4]'(by decide)]
    let tmp_c2 := #v[xn2[2]'(by decide), 0, yn2[2]'(by decide), 0,
      xn2[5]'(by decide), 0, yn2[5]'(by decide), 0]
    let tmp_c3 := #v[xn1[2]'(by decide), 0, yn1[2]'(by decide), 0,
      xn1[5]'(by decide), 0, yn1[5]'(by decide), 0]
    have v54Value : v54 = tmp_c0.map PoisonOr.value := by
      denote_shuffle hv54 with quadMulResult, quadVec, Quad.vector, quadElemVec, Vector.getElem_map
    have v55Value : v55 = tmp_c1.map PoisonOr.value := by
      denote_shuffle hv55 with quadMulResult, quadVec, Quad.vector, quadElemVec, Vector.getElem_map
    have v56Value : v56 = tmp_c2.map PoisonOr.value := by
      denote_shuffle hv56 with quadMulResult, quadVec, Quad.vector, quadElemVec, Vector.getElem_map
    have v57Value : v57 = tmp_c3.map PoisonOr.value := by
      denote_shuffle hv57 with quadMulResult, quadVec, Quad.vector, quadElemVec, Vector.getElem_map
    subst v54Value v55Value v56Value v57Value

    -- %58-%61: the four `vpermi2var`s, each gathering one element's six limbs
    -- (lanes 6 and 7 zero), written out lane by lane
    let xn2z := #v[xn2[0]'(by decide), xn2[1]'(by decide), xn2[2]'(by decide), xn2[3]'(by decide), xn2[4]'(by decide), xn2[5]'(by decide), 0, 0]
    let xn1z := #v[xn1[0]'(by decide), xn1[1]'(by decide), xn1[2]'(by decide), xn1[3]'(by decide), xn1[4]'(by decide), xn1[5]'(by decide), 0, 0]
    let yn2z := #v[yn2[0]'(by decide), yn2[1]'(by decide), yn2[2]'(by decide), yn2[3]'(by decide), yn2[4]'(by decide), yn2[5]'(by decide), 0, 0]
    let yn1z := #v[yn1[0]'(by decide), yn1[1]'(by decide), yn1[2]'(by decide), yn1[3]'(by decide), yn1[4]'(by decide), yn1[5]'(by decide), 0, 0]
    have v58Value : v58 = xn2z.map PoisonOr.value := by ge_permi hv58 with Vector.getElem_map, Quad.vector, quadElemVec
    have v59Value : v59 = xn1z.map PoisonOr.value := by ge_permi hv59 with Vector.getElem_map, Quad.vector, quadElemVec
    have v60Value : v60 = yn2z.map PoisonOr.value := by ge_permi hv60 with Vector.getElem_map, Quad.vector, quadElemVec
    have v61Value : v61 = yn1z.map PoisonOr.value := by ge_permi hv61 with Vector.getElem_map, Quad.vector, quadElemVec
    subst v58Value v59Value v60Value v61Value
    denote_clear v 54 61

    -- `fd_r43x6_sub_fast`: `xn1 - xn2 + p`, lane by lane (lanes 6 and 7 are `0 - 0 + 0`)
    let xDiff := #v[xn1[0]'(by decide) - xn2[0]'(by decide) + pVec[0]'(by decide), xn1[1]'(by decide) - xn2[1]'(by decide) + pVec[1]'(by decide), xn1[2]'(by decide) - xn2[2]'(by decide) + pVec[2]'(by decide), xn1[3]'(by decide) - xn2[3]'(by decide) + pVec[3]'(by decide), xn1[4]'(by decide) - xn2[4]'(by decide) + pVec[4]'(by decide), xn1[5]'(by decide) - xn2[5]'(by decide) + pVec[5]'(by decide), 0, 0]
    let yDiff := #v[yn1[0]'(by decide) - yn2[0]'(by decide) + pVec[0]'(by decide), yn1[1]'(by decide) - yn2[1]'(by decide) + pVec[1]'(by decide), yn1[2]'(by decide) - yn2[2]'(by decide) + pVec[2]'(by decide), yn1[3]'(by decide) - yn2[3]'(by decide) + pVec[3]'(by decide), yn1[4]'(by decide) - yn2[4]'(by decide) + pVec[4]'(by decide), yn1[5]'(by decide) - yn2[5]'(by decide) + pVec[5]'(by decide), 0, 0]

    -- the differences are `s62`: lane by lane they are `subFast` of the four
    -- cross products, which the tight `u46` count bounds by `7000·2^49`
    have hM : ∀ (j : Fin 4) (k : Fin 6), quadMulLimb XShuff YShuff j k < 7000 * 2 ^ 49 :=
      fun j k => quadMulLimb_lt_u46_tight XShuff YShuff
        hXShuff03 hXShuff14 hXShuff25 hYShuff03 hYShuff14 hYShuff25 j k
    have hxd : xDiff = subFastVec (quadMulLimb XShuff YShuff 1) (quadMulLimb XShuff YShuff 0) := by
      apply Vector.ext
      intro i hi
      interval_cases i <;> simp [xDiff, xn1, xn2, pVec, resultQuad, subFastVec, Quad.vector, quadElemVec, quadMulResult, quadVec, ← sub_add_lane, subFast, pLimbs, R43x6.limbs6, BitVec.ofInt_ofNat]
    have hyd : yDiff = subFastVec (quadMulLimb XShuff YShuff 3) (quadMulLimb XShuff YShuff 2) := by
      apply Vector.ext
      intro i hi
      interval_cases i <;> simp [yDiff, yn1, yn2, pVec, resultQuad, subFastVec, Quad.vector, quadElemVec, quadMulResult, quadVec, ← sub_add_lane, subFast, pLimbs, R43x6.limbs6, BitVec.ofInt_ofNat]
    have hxs62 : R43x6.S62 (xDiff.take R43x6.limbCount) := hxd ▸ s62_subFastVec (hM 1) (hM 0)
    have hys62 : R43x6.S62 (yDiff.take R43x6.limbCount) := hyd ▸ s62_subFastVec (hM 3) (hM 2)

    let P := X.toPoint
    let Q := Y.toPoint
    have hP : x.toPoint = P := rfl
    have hQ : y.toPoint = Q := rfl

    have xDiffVal : R43x6.decode' xDiff = ((P.X * Q.Z) - (P.Z * Q.X)) := by
      let xn1Val := decodeVec (by omega) xn1
      let xn2Val := decodeVec (by omega) xn2
      let pVal := decodeVec (by omega) pVec

      -- `fd_r43x6_p()` decodes to `p`, which is `0` in the field
      have pValIsP : pVal = 0 := by
        have hp : (decodeNat (fun i : Fin 6 =>
            (pVec[i.val]'(lt_of_lt_of_le i.isLt (by omega : 6 ≤ 8))).toNat) : ℕ) = p := by
          simp [decodeNat_eq, pVec]; rfl
        show ((decodeNat _ : ℕ) : ZMod p) = 0
        rw [hp]; exact ZMod.natCast_self p

      -- an element of the result QUAD decodes to its specified limbs
      have hres : ∀ j : Fin 4, decodeVec (le_refl _) (resultQuad.vector j)
          = ((decodeNat (quadMulLimb XShuff YShuff j) : ℕ) : ZMod p) := by
        intro j
        show quadElem resultQuad j = _
        simp only [quadElem, Quad.vectorFunc, Function.comp, laneFunc_vector]
        congr 2
        funext k
        exact quadMul_limbs XShuff YShuff hXShuff03' hXShuff14' hXShuff25' hYShuff03' hYShuff14' hYShuff25' j k

      have xDiffSub : ((R43x6.decode' xDiff : ℤ) : ZMod p) = xn1Val - xn2Val + pVal := by
        rw [show xn1Val = _ from hres 1, show xn2Val = _ from hres 0, pValIsP, add_zero, hxd,
          ← R43x6.decodeLimbs_extractLimbs, extractLimbs_subFastVec (hM 1) (hM 0),
          intCast_decodeLimbs_subFast]

      -- the permuted multiply's elements 1 and 0 are `xn1 = X₁·Z₂` and `xn2 = Z₁·X₂`
      obtain ⟨hs0, hs1, _, _⟩ := quadMulLimb_shuf x y
      have xn1Value : xn1Val = P.X * Q.Z := by
        rw [show xn1Val = _ from hres 1, show quadMulLimb XShuff YShuff 1 = xn1Limb x y from hs1,
          decodeLimbs_xn1Limb_zmod, hP, hQ]
      have xn2Value : xn2Val = P.Z * Q.X := by
        rw [show xn2Val = _ from hres 0, show quadMulLimb XShuff YShuff 0 = xn2Limb x y from hs0,
          decodeLimbs_xn2Limb_zmod, hP, hQ]
      rw [xDiffSub, xn1Value, xn2Value, pValIsP, add_zero]

    have yDiffVal : R43x6.decode' yDiff = ((P.Y * Q.Z) - (P.Z * Q.Y)) := by
      let yn1Val := decodeVec (by omega) yn1
      let yn2Val := decodeVec (by omega) yn2
      let pVal := decodeVec (by omega) pVec

      -- `fd_r43x6_p()` decodes to `p`, which is `0` in the field
      have pValIsP : pVal = 0 := by
        have hp : (decodeNat (fun i : Fin 6 =>
            (pVec[i.val]'(lt_of_lt_of_le i.isLt (by omega : 6 ≤ 8))).toNat) : ℕ) = p := by
          simp [decodeNat_eq, pVec]; rfl
        show ((decodeNat _ : ℕ) : ZMod p) = 0
        rw [hp]; exact ZMod.natCast_self p

      -- an element of the result QUAD decodes to its specified limbs
      have hres : ∀ j : Fin 4, decodeVec (le_refl _) (resultQuad.vector j)
          = ((decodeNat (quadMulLimb XShuff YShuff j) : ℕ) : ZMod p) := by
        intro j
        show quadElem resultQuad j = _
        simp only [quadElem, Quad.vectorFunc, Function.comp, laneFunc_vector]
        rw [show quadLimb resultQuad.v03 resultQuad.v14 resultQuad.v25 j
            = quadMulLimb XShuff YShuff j from funext fun k =>
              quadMul_limbs XShuff YShuff hXShuff03' hXShuff14' hXShuff25' hYShuff03' hYShuff14' hYShuff25' j k]

      have yDiffSub : ((R43x6.decode' yDiff : ℤ) : ZMod p) = yn1Val - yn2Val + pVal := by
        rw [show yn1Val = _ from hres 3, show yn2Val = _ from hres 2, pValIsP, add_zero, hyd,
          ← R43x6.decodeLimbs_extractLimbs, extractLimbs_subFastVec (hM 3) (hM 2),
          intCast_decodeLimbs_subFast]

      -- the permuted multiply's elements 3 and 2 are `yn1 = Y₁·Z₂` and `yn2 = Z₁·Y₂`
      obtain ⟨_, _, hs2, hs3⟩ := quadMulLimb_shuf x y
      have yn1Value : yn1Val = P.Y * Q.Z := by
        rw [show yn1Val = _ from hres 3, show quadMulLimb XShuff YShuff 3 = yn1Limb x y from hs3,
          decodeLimbs_yn1Limb_zmod, hP, hQ]
      have yn2Value : yn2Val = P.Z * Q.Y := by
        rw [show yn2Val = _ from hres 2, show quadMulLimb XShuff YShuff 2 = yn2Limb x y from hs2,
          decodeLimbs_yn2Limb_zmod, hP, hQ]
      rw [yDiffSub, yn1Value, yn2Value, pValIsP, add_zero]

    denote_step_all v 63
    have v63Value : v63 = xDiff.map PoisonOr.value := by
      simp only [hv62, hv63, Expr.denoteOp1, Expr.denoteOpPure]
      simp_peephole
      simp only [HVector.head]
      apply Vector.ext
      intro i hi
      interval_cases i
      all_goals simp +zetaDelta [InstCombine.binaryDenote, LLVM.sub, LLVM.sub?, LLVM.add, LLVM.add?,
          Vector.getElem_ofFn, Vector.getElem_mk, List.getElem_toArray,
          List.getElem_cons_zero, List.getElem_cons_succ]
    subst v63Value
    denote_clear v 62 63

    denote_step_all v 65
    -- %64: the first `fd_r43x6_is_nonzero` call, a single rewrite of the callee's
    -- spec: the zero test is in the field
    let xDiffNonzero := PoisonOr.value (if ((R43x6.decode' xDiff : ℤ) : ZMod p) = 0 then 0#32 else 1#32)
    have v64Value : v64 = xDiffNonzero := by
      simp only [hv64, Expr.denoteOp1, Expr.denoteOpPure]
      set_option maxRecDepth 100000 in
      show HVector.head (fd_r43x6_is_nonzero.denote (Ctxt.Valuation.singleton
        (xDiff.map PoisonOr.value))) = _
      rw [spec_denote_fd_r43x6_is_nonzero _ hxs62]
      rfl
    subst v64Value

    let xDiffZero := PoisonOr.value (if ((R43x6.decode' xDiff : ℤ) : ZMod p) = 0 then (-1#32) else (-2#32))
    have v65Value : v65 = xDiffZero := by
      simp only [hv65, Expr.denoteOp1, Expr.denoteOpPure, HVector.head]
      simp_peephole
      -- `0 ^^^ -1 = -1`, `1 ^^^ -1 = -2`, one branch each
      simp [LLVM.xor, LLVM.xor?, xDiffNonzero, xDiffZero, neg1]
      split <;> rfl
    subst v65Value
    denote_clear v 64 65

    denote_step_all v 67
    have v67Value : v67 = yDiff.map PoisonOr.value := by
      simp only [hv66, hv67, Expr.denoteOp1, Expr.denoteOpPure]
      simp_peephole
      simp only [HVector.head]
      apply Vector.ext
      intro i hi
      interval_cases i
      all_goals simp +zetaDelta [InstCombine.binaryDenote, LLVM.sub, LLVM.sub?, LLVM.add, LLVM.add?,
          Vector.getElem_ofFn, Vector.getElem_mk, List.getElem_toArray,
          List.getElem_cons_zero, List.getElem_cons_succ]
    subst v67Value
    denote_clear v 66 67

    denote_step_all v 69
    -- %68: the second `fd_r43x6_is_nonzero` call, the same single rewrite
    let yDiffNonzero := PoisonOr.value (if ((R43x6.decode' yDiff : ℤ) : ZMod p) = 0 then 0#32 else 1#32)
    have v68Value : v68 = yDiffNonzero := by
      simp only [hv68, Expr.denoteOp1, Expr.denoteOpPure]
      set_option maxRecDepth 100000 in
      show HVector.head (fd_r43x6_is_nonzero.denote (Ctxt.Valuation.singleton
        (yDiff.map PoisonOr.value))) = _
      rw [spec_denote_fd_r43x6_is_nonzero _ hys62]
      rfl
    subst v68Value

    let yDiffZero := PoisonOr.value (if ((R43x6.decode' yDiff : ℤ) : ZMod p) = 0 then (1#32) else (0#32))
    have v69Value : v69 = yDiffZero := by
      simp only [hv69, Expr.denoteOp1, Expr.denoteOpPure, HVector.head]
      simp_peephole
      simp [LLVM.xor, LLVM.xor?, yDiffNonzero, yDiffZero]
      split <;> rfl
    subst v69Value
    denote_clear v 68 69

    denote_step_all v
    simp only [Com.denote_rets]
    simp only [hv70, Expr.denoteOp1, Expr.denoteOpPure, HVector.head]
    simp_peephole

    simp
    constructor
    · simp [LLVM.and, LLVM.and?, xDiffZero, yDiffZero, geIsEq, xDiffVal, yDiffVal, P, Q, X, Y]
      have novec (e: Quad) : e.PointVecs.toPoint = e.toPoint := rfl
      rw [novec]
      rw [novec]
      by_cases h: ((x.toPoint.X * y.toPoint.Z) - (x.toPoint.Z * y.toPoint.X) = 0) <;> by_cases h': (x.toPoint.Y * y.toPoint.Z - x.toPoint.Z * y.toPoint.Y = 0) <;> simp [h, h']
    · rfl

/-! ## The model decides equality -/

/-- `GeIsEqDecides`: the model's two zero tests are `samePoint_iff_cross_sub_eq_zero`
with the second products commuted. -/
theorem geIsEqDecides (x y : Quad) : GeIsEqDecides x y := by
  intro _ _ _ _ _ _ hZ1 hZ2
  simp only [geIsEq, Point.samePoint_iff_cross_sub_eq_zero hZ1 hZ2]
  rw [mul_comm y.toPoint.X, mul_comm y.toPoint.Y]

/-- **Specification of `fd_r43x6_ge_is_eq`**: on two `u46` QUADs whose `Z`s
are invertible, the function returns `1` exactly when they represent the same
curve point and `0` otherwise, and leaves the stack as it found it. The
composition of `run_fd_r43x6_ge_is_eq` with `geIsEqDecides`; the model does
not appear. -/
theorem spec_run_fd_r43x6_ge_is_eq (x y : Quad)
    (hx03 : R43x6.U46 x.v03) (hx14 : R43x6.U46 x.v14) (hx25 : R43x6.U46 x.v25)
    (hy03 : R43x6.U46 y.v03) (hy14 : R43x6.U46 y.v14) (hy25 : R43x6.U46 y.v25)
    (hZ1 : IsUnit x.toPoint.Z) (hZ2 : IsUnit y.toPoint.Z)
    (s : GlobalState) (hs : s.WF) :
    ∃ s', StateT.run (runFunction (fd_r43x6_ge_is_eq.denote (quadDualValuation x y))) s
        = .value ([PoisonOr.value (if x.toPoint.SamePoint y.toPoint then 1 else 0)]ₕ, s')
      ∧ s' ≈ s := by
  rw [← geIsEqDecides x y hx03 hx14 hx25 hy03 hy14 hy25 hZ1 hZ2]
  exact run_fd_r43x6_ge_is_eq x y hx03 hx14 hx25 hy03 hy14 hy25 s hs

end Firedancer.Avx512

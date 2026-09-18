/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_neg

/-!
# `fd_ed25519_point_neg( a, a )` conformance (AVX-512)

In place, as `fd_ed25519_verify` calls it. The region loads `a`'s `14` and `25` vectors a second
time after storing into `r`, but each store lies in a window below the vector it reloads, so the
reloads still see the input: the proof is `fd_ed25519_point_neg_conforms`'s, with those two loads
read through the spliced block.
-/

@[expose] public section

namespace Firedancer.Avx512

open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- **`fd_ed25519_point_neg( a, a )`**: `fd_ed25519_point_neg_spec` with `r := a`. -/
abbrev fd_ed25519_point_neg_self_spec (a : Pointer) (s : GlobalState) (ha : IsQuadPtr s.mem a) :
    Prop :=
  let invocation :=
    runFunction (fd_ed25519_point_neg.denote (Ctxt.Valuation.ofHVector [.value a, .value a]ₕ))
  let result := StateT.run invocation s
  let q := readQuad ha
  let P := q.toPoint
  q.NegBounds 0 →
    q.NegBounds 3 →
      ∃ s' : GlobalState,
        result = .value ([.value a]ₕ, s') ∧
          ∃ q' : Quad,
            let output_state : GlobalState := { s with mem := s.mem.splice a q'.BV }
            output_state ≈ s' ∧
              q'.toPoint = { X := -P.X, Y := P.Y, Z := P.Z, T := -P.T } ∧ ∀ j, q'.NegBounds j

open PointNeg in
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
theorem fd_ed25519_point_neg_self_conforms (a : Pointer) (s : GlobalState) (hs : s.WF)
    (ha : IsQuadPtr s.mem a) : fd_ed25519_point_neg_self_spec a s ha := by
  simp only [fd_ed25519_point_neg_self_spec, Cfg.denote]
  have hr := ha
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
  -- `%58`/`%59`: the `03` lane subtract, stored to `a`.
  denote_step_reduce v 59 only [hv25] fold
  have hN03 : v59 = (negQuad (readQuad ha)).v03.map PoisonOr.value := denote_negLanes rfl rfl hv59
  subst hN03
  refine
    name_of ({ s with mem := s.mem.splice a (vecBV (negQuad (readQuad ha)).v03) }) fun s₁ hs₁ => ?_
  peel_store (negQuad (readQuad ha)).v03, a, hr.1, s as s₁ := hs₁
  have f₁ : Fits s₁.mem a (3 * 8 * 64) := hs₁ ▸ fits_splice hr.1
  -- `%60 … %63`: `a`'s `14` again: the store above wrote the 512 bits before it.
  let ablk₁ : LiveBlock :=
    { ablk with bytes := spliceBits ablk.bytes a.offsetInBits (vecBV (negQuad (readQuad ha)).v03) }
  have hE₁ : s₁.mem[aField.id]? = some (.live ablk₁) := by
    rw [hs₁]; exact getElem?_splice_self hablkE
  have hlen₁ : ablk₁.lengthInBits = ablk.lengthInBits := rfl
  peel_load (.vector 8 (.bitvec (.concrete 64))), ablk₁, aField, hE₁, s₁
  rw [hoffA, extractLsb'_spliceBits_of_disjoint (w := 512) (w' := 512) _ _ _ _ (.inr (by omega)),
    unflatten_readQuad_v14 ha halive]
  denote_step_reduce v 62 only [hv34] fold
  have hN14 : v62 = (negQuad (readQuad ha)).v14.map PoisonOr.value := denote_negLanes rfl rfl hv62
  subst hN14
  peel_gep 64 with a, f₁, s₁ as rField
  have fR : Fits s₁.mem rField 1024 := Fits.mono hrField (by simp)
  refine
    name_of ({ s₁ with mem := s₁.mem.splice rField (vecBV (negQuad (readQuad ha)).v14) })
      fun s₂ hs₂ => ?_
  peel_store (negQuad (readQuad ha)).v14, rField, fR, s₁ as s₂ := hs₂
  have f₂ : Fits s₂.mem a (3 * 8 * 64) := hs₂ ▸ fits_splice f₁
  -- `%64 … %67`: the same for `25`.
  let ablk₂ : LiveBlock :=
    { ablk₁ with
      bytes := spliceBits ablk₁.bytes rField.offsetInBits (vecBV (negQuad (readQuad ha)).v14) }
  have hE₂ : s₂.mem[aField25.id]? = some (.live ablk₂) := by
    rw [hs₂]; exact getElem?_splice_self hE₁
  have hoffR : rField.offsetInBits = a.offsetInBits + 512 := hoffA
  have hlen₂ : ablk₂.lengthInBits = ablk.lengthInBits := rfl
  peel_load (.vector 8 (.bitvec (.concrete 64))), ablk₂, aField25, hE₂, s₂
  have hB₂ :
    ablk₂.bytes =
      spliceBits (spliceBits ablk.bytes a.offsetInBits (vecBV (negQuad (readQuad ha)).v03))
        (a.offsetInBits + 512) (vecBV (negQuad (readQuad ha)).v14) := by
    rw [← hoffR]
  rw [hB₂, hoffA25,
    extractLsb'_spliceBits_of_disjoint (w := 512) (w' := 512) _ _ _ _ (.inr (by omega)),
    extractLsb'_spliceBits_of_disjoint (w := 512) (w' := 512) _ _ _ _ (.inr (by omega)),
    unflatten_readQuad_v25 ha halive]
  denote_step_reduce v 66 only [hv43] fold
  have hN25 : v66 = (negQuad (readQuad ha)).v25.map PoisonOr.value := denote_negLanes rfl rfl hv66
  subst hN25
  peel_gep 128 with a, f₂, s₂ as rField25
  have fR25 : Fits s₂.mem rField25 512 := Fits.mono hrField25 (by simp)
  -- `%68 … %78`: `FD_R43X6_QUAD_FOLD_UNSIGNED`, one store per vector.
  denote_step_reduce v 74 only [hv4, hv3, hv52, hv1] fold
  have hF03 : v74 = (foldQuad (negQuad (readQuad ha))).v03.map PoisonOr.value :=
    denote_quadFold_v03 (q := negQuad (readQuad ha)) rfl rfl rfl rfl hv74
  subst hF03
  refine
    name_of ({ s₂ with mem := s₂.mem.splice a (vecBV (foldQuad (negQuad (readQuad ha))).v03) })
      fun s₃ hs₃ => ?_
  peel_store (foldQuad (negQuad (readQuad ha))).v03, a, f₂, s₂ as s₃ := hs₃
  denote_step_reduce v 76 only [hv1] fold
  have hF14 : v76 = (foldQuad (negQuad (readQuad ha))).v14.map PoisonOr.value :=
    denote_quadFold_v14 (q := negQuad (readQuad ha)) hv68 rfl hv76
  subst hF14
  have f₄ : Fits s₃.mem rField (8 * 64) := by
    rw [hs₃, hs₂]; exact fits_splice (fits_splice (Fits.mono fR (by omega)))
  refine
    name_of ({ s₃ with mem := s₃.mem.splice rField (vecBV (foldQuad (negQuad (readQuad ha))).v14) })
      fun s₄ hs₄ => ?_
  peel_store (foldQuad (negQuad (readQuad ha))).v14, rField, f₄, s₃ as s₄ := hs₄
  denote_step_reduce v 78 only [hv0] fold
  have hF25 : v78 = (foldQuad (negQuad (readQuad ha))).v25.map PoisonOr.value :=
    denote_quadFold_v25 (q := negQuad (readQuad ha)) hv69 rfl hv78
  subst hF25
  have f₅ : Fits s₄.mem rField25 (8 * 64) := by
    rw [hs₄, hs₃]; exact fits_splice (fits_splice fR25)
  refine
    name_of
      ({ s₄ with mem := s₄.mem.splice rField25 (vecBV (foldQuad (negQuad (readQuad ha))).v25) })
      fun s₅ hs₅ => ?_
  peel_store (foldQuad (negQuad (readQuad ha))).v25, rField25, f₅, s₄ as s₅ := hs₅
  -- `return %arg0`, in `s₅`
  refine ⟨s₅, by simp_return, ?_⟩
  /- The region has returned. What remains is that its five stores are the one
  the spec states, and what that store holds. -/
  have hmem : s₅.mem = negMem s.mem a (readQuad ha) := by
    -- `unfold` + `dsimp`, not `rfl`: unification would unfold the splices
    rw [hs₅, hs₄, hs₃, hs₂, hs₁]; unfold negMem; dsimp only
  rw [hmem]
  -- `a`'s two field pointers are 512 and 1024 bits in: `hr.2` rules out wrapping
  have h64 : (a.withOffset 64).offsetInBits = a.offsetInBits + 512 := by
    have hb := hr.2
    simp only [Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add,
      show (64 : BitVec 64).toNat = 64 from rfl] at hb ⊢
    omega
  have h128 : (a.withOffset 128).offsetInBits = a.offsetInBits + 1024 := by
    have hb := hr.2
    simp only [Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add,
      show (128 : BitVec 64).toNat = 128 from rfl] at hb ⊢
    omega
  -- the region allocates nothing, so the frame kill at `return` is invisible
  have hnone :
    ∀ c : BlockId, s.alloc.nextFreeBlock ≤ c.id → (negMem s.mem a (readQuad ha)).live? c = none :=
    fun c hc => by
    unfold negMem
    exact
      live?_splice_eq_none
        (live?_splice_eq_none
          (live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none (hs c hc)))))
  have hkill := killFrom_equiv_of_none (s := s) (m := negMem s.mem a (readQuad ha)) hnone
  have hcol := negMem_equiv (s := s) (readQuad ha) h64 h128
  exact
    ⟨foldQuad (negQuad (readQuad ha)),
      GlobalState.Equiv.trans (GlobalState.Equiv.symm hcol) (GlobalState.Equiv.symm hkill), by
      rw [toPoint_foldQuad, toPoint_negQuad _ hb0 hb3], foldQuad_negBounds _⟩

end Firedancer.Avx512

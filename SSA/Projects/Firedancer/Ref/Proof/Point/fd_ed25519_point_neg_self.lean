/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Spec.Point.fd_ed25519_point_neg
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_neg
import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_point_sub_with_opts
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Point
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_neg
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_set

/-!
# `fd_ed25519_point_neg( a, a )` conformance

In place. `fd_f25519_neg` already allows `r = a`; `fd_f25519_set( o, o )` loads
limb `i` after storing limbs `< i` only, so each load still sees the original.
Each point coordinate is read before its own store and the stores are disjoint.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- The bits a load at limb `i` sees, given that limb's `readLimb?`. -/
theorem loadBits {m : MemoryState} {p : Pointer} {blk : LiveBlock}
    (hblk : m[p.id]? = some (Block.live blk)) {i : Fin 5} {v : ℕ}
    (hl : readLimb? p i m = some v) {off : ℕ} (hoff : off = p.offsetInBits + 64 * i.toNat) :
    blk.bytes.extractLsb' off 64 = BitVec.ofNat 64 v := by
  subst hoff
  simp only [readLimb?, MemoryState.live?, hblk, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Option.some.injEq] at hl
  rw [← hl, BitVec.ofNat_toNat, BitVec.setWidth_eq]

set_option maxHeartbeats 800000 in
/-- **`fd_f25519_set( o, o )`** stores back what it loads: `fd_f25519_set_spec` at `q := o`. -/
theorem fd_f25519_set_self_conforms (o : Pointer) (s : GlobalState) (hs : s.WF)
    (ho : IsFieldElemPtr s.mem o) :
    ∃ out : BitVec (5 * 64),
      (∃ s' : GlobalState, StateT.run (runFunction (fd_f25519_set.denote
          (Ctxt.Valuation.ofHVector [.value o, .value o]ₕ))) s = .value ([.value o]ₕ, s')
        ∧ ({ s with mem := s.mem.splice o out } : GlobalState) ≈ s')
      ∧ ∀ i : Fin 5, readLimb? o i (s.mem.splice o out) = readLimb? o i s.mem := by
  simp only [Cfg.denote]

  obtain ⟨qblk, hqblk, hqlen⟩ := id ho.left
  obtain ⟨qinput, hqinput⟩ := exists_limbs hqblk
  let outputBV := BitVec.ofNat 64 ∘ qinput

  refine ⟨packLimbs outputBV, ?_⟩

  constructor
  case right =>
    intro i
    rw [limbReadbackPack _ _ _ ho.left i, hqinput i]
    have hlt : qinput i < 2 ^ 64 := by
      have h := hqinput i
      simp only [readLimb?, MemoryState.live?, hqblk, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, Option.some.injEq] at h
      rw [← h]; exact BitVec.isLt _
    simp only [outputBV, Function.comp_apply, BitVec.toNat_ofNat]
    exact congrArg some (Nat.mod_eq_of_lt hlt)

  obtain ⟨outMem, houtMem⟩ : ∃ m : MemoryState,
      m = ((((s.mem.splice o (outputBV 0)).splice (o.withOffset 8) (outputBV 1)).splice
            (o.withOffset 16) (outputBV 2)).splice (o.withOffset 24) (outputBV 3)).splice
            (o.withOffset 32) (outputBV 4) := ⟨_, rfl⟩
  refine ⟨s.popFrame outMem, run_runFunction (s' := { s with mem := outMem }) ?_, ?equiv⟩
  case equiv =>
    have hnone : ∀ (b : BlockId), s.alloc.nextFreeBlock ≤ b.id → outMem.live? b = none := by
      rw [houtMem]
      exact fun b hb => live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none
        (live?_splice_eq_none (live?_splice_eq_none (hs b hb)))))
    refine GlobalState.Equiv.trans ?_ (GlobalState.Equiv.symm
      (killFrom_equiv_of_none (s := s) (m := outMem) hnone))
    rw [houtMem]
    exact GlobalState.Equiv.symm
      (splice5_equiv (outputBV 0) (outputBV 1) (outputBV 2) (outputBV 3) (outputBV 4) ho)

  -- limb offsets in bits; `ho.right` rules out wrapping
  have ob : ∀ (k : ℕ) (d : BitVec 64), k ≤ 4 → d.toNat = 8 * k →
      (o.withOffset d).offsetInBits = o.offsetInBits + 64 * k :=
    fun _ _ hk hd => limbOffsetInBits ho.right hk hd

  denote_expose

  -- limb 0: load off the base pointer, store, both still in `s`
  peel_limb 0, o, ho.left, qblk, hqblk, qlimb
  rw [show qlimb₀ = outputBV 0 from by
    rw [hqlimb₀]; exact limbBits hqblk hqinput 0 (by simp)]
  peel_store (outputBV 0), o, ho.left, s
  obtain ⟨s₁, hs₁⟩ : ∃ t : GlobalState, { s with mem := s.mem.splice o (outputBV 0) } = t := ⟨_, rfl⟩
  rw [hs₁]
  have f₁ : Fits s₁.mem o (5 * 64) := hs₁ ▸ fits_splice ho.left
  have e₁ : ∀ j : Fin 5, 1 ≤ j.toNat → readLimb? o j s₁.mem = readLimb? o j s.mem :=
    fun j hj => by rw [← hs₁]; exact readLimb?_splice_of_disjoint j (.inr (.inl (by omega)))

  -- limb 1: the store to limb 0 misses it
  peel_gep_limb 1, o, f₁, s₁, q
  obtain ⟨qb₁, hqb₁, hql₁⟩ := id hq₁
  peel_load (.bitvec (.concrete 64)), qb₁, q₁, hqb₁, s₁
  rw [show qb₁.bytes.extractLsb' (q₁).offsetInBits 64 = outputBV 1 from
    loadBits (p := o) hqb₁ ((e₁ 1 (by decide)).trans (hqinput 1)) (ob 1 8#64 (by omega) rfl)]
  peel_gep_limb 1, o, f₁, s₁, o
  peel_store (outputBV 1), o₁, ho₁, s₁
  obtain ⟨s₂, hs₂⟩ : ∃ t : GlobalState, { s₁ with mem := s₁.mem.splice o₁ (outputBV 1) } = t := ⟨_, rfl⟩
  rw [hs₂]
  have f₂ : Fits s₂.mem o (5 * 64) := hs₂ ▸ fits_splice f₁
  have e₂ : ∀ j : Fin 5, 2 ≤ j.toNat → readLimb? o j s₂.mem = readLimb? o j s₁.mem :=
    fun j hj => by
      rw [← hs₂]
      exact readLimb?_splice_of_disjoint j (.inr (.inl (by
        have h : o₁.offsetInBits = o.offsetInBits + 64 * 1 := ob 1 8#64 (by omega) rfl
        omega)))

  -- limb 2
  peel_gep_limb 2, o, f₂, s₂, q
  obtain ⟨qb₂, hqb₂, hql₂⟩ := id hq₂
  peel_load (.bitvec (.concrete 64)), qb₂, q₂, hqb₂, s₂
  rw [show qb₂.bytes.extractLsb' (q₂).offsetInBits 64 = outputBV 2 from
    loadBits (p := o) hqb₂ ((e₂ 2 (by decide)).trans ((e₁ 2 (by decide)).trans (hqinput 2)))
      (ob 2 16#64 (by omega) rfl)]
  peel_gep_limb 2, o, f₂, s₂, o
  peel_store (outputBV 2), o₂, ho₂, s₂
  obtain ⟨s₃, hs₃⟩ : ∃ t : GlobalState, { s₂ with mem := s₂.mem.splice o₂ (outputBV 2) } = t := ⟨_, rfl⟩
  rw [hs₃]
  have f₃ : Fits s₃.mem o (5 * 64) := hs₃ ▸ fits_splice f₂
  have e₃ : ∀ j : Fin 5, 3 ≤ j.toNat → readLimb? o j s₃.mem = readLimb? o j s₂.mem :=
    fun j hj => by
      rw [← hs₃]
      exact readLimb?_splice_of_disjoint j (.inr (.inl (by
        have h : o₂.offsetInBits = o.offsetInBits + 64 * 2 := ob 2 16#64 (by omega) rfl
        omega)))

  -- limb 3
  peel_gep_limb 3, o, f₃, s₃, q
  obtain ⟨qb₃, hqb₃, hql₃⟩ := id hq₃
  peel_load (.bitvec (.concrete 64)), qb₃, q₃, hqb₃, s₃
  rw [show qb₃.bytes.extractLsb' (q₃).offsetInBits 64 = outputBV 3 from
    loadBits (p := o) hqb₃ ((e₃ 3 (by decide)).trans ((e₂ 3 (by decide)).trans
      ((e₁ 3 (by decide)).trans (hqinput 3)))) (ob 3 24#64 (by omega) rfl)]
  peel_gep_limb 3, o, f₃, s₃, o
  peel_store (outputBV 3), o₃, ho₃, s₃
  obtain ⟨s₄, hs₄⟩ : ∃ t : GlobalState, { s₃ with mem := s₃.mem.splice o₃ (outputBV 3) } = t := ⟨_, rfl⟩
  rw [hs₄]
  have f₄ : Fits s₄.mem o (5 * 64) := hs₄ ▸ fits_splice f₃
  have e₄ : ∀ j : Fin 5, 4 ≤ j.toNat → readLimb? o j s₄.mem = readLimb? o j s₃.mem :=
    fun j hj => by
      rw [← hs₄]
      exact readLimb?_splice_of_disjoint j (.inr (.inl (by
        have h : o₃.offsetInBits = o.offsetInBits + 64 * 3 := ob 3 24#64 (by omega) rfl
        omega)))

  -- limb 4
  peel_gep_limb 4, o, f₄, s₄, q
  obtain ⟨qb₄, hqb₄, hql₄⟩ := id hq₄
  peel_load (.bitvec (.concrete 64)), qb₄, q₄, hqb₄, s₄
  rw [show qb₄.bytes.extractLsb' (q₄).offsetInBits 64 = outputBV 4 from
    loadBits (p := o) hqb₄ ((e₄ 4 (by decide)).trans ((e₃ 4 (by decide)).trans
      ((e₂ 4 (by decide)).trans ((e₁ 4 (by decide)).trans (hqinput 4)))))
      (ob 4 32#64 (by omega) rfl)]
  peel_gep_limb 4, o, f₄, s₄, o
  peel_store (outputBV 4), o₄, ho₄, s₄
  obtain ⟨s₅, hs₅⟩ : ∃ t : GlobalState, { s₄ with mem := s₄.mem.splice o₄ (outputBV 4) } = t := ⟨_, rfl⟩
  rw [hs₅]

  simp only [BlockCom.denote_term, Terminator.denote_ret, houtMem,
    ← hs₁, ← hs₂, ← hs₃, ← hs₄, ← hs₅, o₁, o₂, o₃, o₄, simp_denote, simp_sllvm]

/-- **`fd_ed25519_point_neg( a, a )`**: `fd_ed25519_point_neg_spec` at `r := a`. -/
abbrev fd_ed25519_point_neg_self_spec (a : Pointer) (s : GlobalState) (ha : IsPointPtr s.mem a) :
    Prop :=
  let invocation := runFunction
    (fd_ed25519_point_neg.denote (Ctxt.Valuation.ofHVector [.value a, .value a]ₕ))
  BiasBounds (isCoordPtr ha 0) → BiasBounds (isCoordPtr ha 2) →
  ∃ s' : GlobalState, StateT.run invocation s = .value ([.value a]ₕ, s') ∧
  ∃ oX oY oZ oT : BitVec (5 * 64),
    let outMem := (((s.mem.splice a oX).splice (a.withOffset 40) oY).splice
      (a.withOffset 120) oZ).splice (a.withOffset 80) oT
    have hpt : IsPointPtr outMem a :=
      isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice ha)))
    ({ s with mem := outMem } : GlobalState) ≈ s'
    ∧ readPoint hpt = (readPoint ha).neg
    ∧ BiasBounds (isCoordPtr hpt 0) ∧ BiasBounds (isCoordPtr hpt 2)
    ∧ (∀ i, readLimb i (isCoordPtr hpt 1) = readLimb i (isCoordPtr ha 1))
    ∧ (∀ i, readLimb i (isCoordPtr hpt 3) = readLimb i (isCoordPtr ha 3))

set_option maxHeartbeats 1600000 in
theorem fd_ed25519_point_neg_self_conforms (a : Pointer) (s : GlobalState) (hs : s.WF)
    (ha : IsPointPtr s.mem a) : fd_ed25519_point_neg_self_spec a s ha := by
  simp only [fd_ed25519_point_neg_self_spec, Cfg.denote]
  intro hbX hbT
  refine run_runFunction' _ ?_

  -- coordinate offsets in bits; `ha.right` rules out wrapping
  have h40 : (a.withOffset 40).offsetInBits = a.offsetInBits + 320 := by
    simpa using withOffset_offsetInBits (off := 40) (by have := ha.2; simp; omega)
  have h80 : (a.withOffset 80).offsetInBits = a.offsetInBits + 640 := by
    simpa using withOffset_offsetInBits (off := 80) (by have := ha.2; simp; omega)
  have h120 : (a.withOffset 120).offsetInBits = a.offsetInBits + 960 := by
    simpa using withOffset_offsetInBits (off := 120) (by have := ha.2; simp; omega)

  denote_expose

  -- `%0`: X ≔ -X, in `s`
  have hc0 : IsFieldElemPtr s.mem a := by
    simpa [Pointer.withOffset] using isCoordPtr ha 0
  have hbX' : BiasBounds hc0 := fun i =>
    (readLimb_eq_of_readLimb? (by rw [coordPtr_zero])).trans_le (hbX i)
  obtain ⟨oX, hvalX, hbndX, u₁, hrun₁, heq₁⟩ := fd_f25519_neg_conforms a a s hs hc0 hc0 hbX'
  peel_call hrun₁
  have hu₁WF : u₁.WF := GlobalState.WF.of_equiv hs.splice heq₁

  -- `%1 … %3`: Y ≔ Y, in `u₁`
  denote_step_reduce v 2 [gepConst, ptradd, LLVM.const?]
  have v1Value : v1 = .value (a.withOffset 40) := by
    simp [hv1, Pointer.withOffset, simp_sllvm]
  have v2Value : v2 = .value (a.withOffset 40) := by
    simp [hv2, Pointer.withOffset, simp_sllvm]
  subst v1Value v2Value
  clear hv1 hv2
  have hc1 : IsFieldElemPtr s.mem (a.withOffset 40) := coordPtr_one a ▸ isCoordPtr ha 1
  have hc1u : IsFieldElemPtr u₁.mem (a.withOffset 40) :=
    ⟨fits_equiv heq₁ (by simpa using fits_splice hc1.1), hc1.2⟩
  obtain ⟨oY, ⟨u₂, hrun₂, heq₂⟩, hcopy₂⟩ :=
    fd_f25519_set_self_conforms (a.withOffset 40) u₁ hu₁WF hc1u
  peel_call hrun₂
  have hu₂WF : u₂.WF := GlobalState.WF.of_equiv hu₁WF.splice heq₂

  -- `%4 … %6`: Z ≔ Z, in `u₂`
  denote_step_reduce v 5 [gepConst, ptradd, LLVM.const?]
  have v4Value : v4 = .value (a.withOffset 120) := by
    simp [hv4, Pointer.withOffset, simp_sllvm]
  have v5Value : v5 = .value (a.withOffset 120) := by
    simp [hv5, Pointer.withOffset, simp_sllvm]
  subst v4Value v5Value
  clear hv4 hv5
  have hc3 : IsFieldElemPtr s.mem (a.withOffset 120) := coordPtr_three a ▸ isCoordPtr ha 3
  have hc3u : IsFieldElemPtr u₂.mem (a.withOffset 120) :=
    ⟨fits_equiv heq₂ (by simpa using fits_splice (fits_equiv heq₁
      (by simpa using fits_splice hc3.1))), hc3.2⟩
  obtain ⟨oZ, ⟨u₃, hrun₃, heq₃⟩, hcopy₃⟩ :=
    fd_f25519_set_self_conforms (a.withOffset 120) u₂ hu₂WF hc3u
  peel_call hrun₃
  have hu₃WF : u₃.WF := GlobalState.WF.of_equiv hu₂WF.splice heq₃

  -- `%7 … %9`: T ≔ -T, in `u₃`
  denote_step_reduce v 8 [gepConst, ptradd, LLVM.const?]
  have v7Value : v7 = .value (a.withOffset 80) := by
    simp [hv7, Pointer.withOffset, simp_sllvm]
  have v8Value : v8 = .value (a.withOffset 80) := by
    simp [hv8, Pointer.withOffset, simp_sllvm]
  subst v7Value v8Value
  clear hv7 hv8
  have hc2 : IsFieldElemPtr s.mem (a.withOffset 80) := by
    simpa [Pointer.withOffset] using isCoordPtr ha 2
  have hc2u : IsFieldElemPtr u₃.mem (a.withOffset 80) :=
    ⟨fits_equiv heq₃ (by simpa using fits_splice (fits_equiv heq₂
      (by simpa using fits_splice (fits_equiv heq₁
        (by simpa using fits_splice hc2.1))))), hc2.2⟩
  -- `T` at `u₃` is `T` at `s`: the three stores so far miss it
  have La : ∀ i : Fin 5, readLimb? (a.withOffset 80) i u₃.mem = readLimb? (a.withOffset 80) i s.mem := by
    intro i
    have hi : i.toNat < 5 := i.isLt
    have e3 := readLimb?_of_equiv heq₃ (a.withOffset 80) i
    dsimp only at e3
    rw [readLimb?_splice_of_disjoint i (.inr (.inr (by rw [h80, h120]; omega)))] at e3
    have e2 := readLimb?_of_equiv heq₂ (a.withOffset 80) i
    dsimp only at e2
    rw [readLimb?_splice_of_disjoint i (.inr (.inl (by rw [h40, h80]; omega)))] at e2
    have e1 := readLimb?_of_equiv heq₁ (a.withOffset 80) i
    dsimp only at e1
    rw [readLimb?_splice_of_disjoint i (.inr (.inl (by rw [h80]; omega)))] at e1
    rw [← e3, ← e2, ← e1]
  have hbTu : BiasBounds hc2u := fun i =>
    (readLimb_eq_of_readLimb? (h' := hc2) (La i)).trans_le (hbT i)
  obtain ⟨oT, hvalT, hbndT, u₄, hrun₄, heq₄⟩ :=
    fd_f25519_neg_conforms (a.withOffset 80) (a.withOffset 80) u₃ hu₃WF hc2u hc2u hbTu
  peel_call hrun₄

  -- `return %arg0`, in `u₄`
  refine ⟨u₄, by simp_return, ?_⟩

  /- The region has returned. What remains is the four stores' readback. -/

  have Lx : ∀ i : Fin 5,
      readLimb? a i ((((s.mem.splice a oX).splice (a.withOffset 40) oY).splice
        (a.withOffset 120) oZ).splice (a.withOffset 80) oT)
        = readLimb? a i (s.mem.splice a oX) := by
    intro i
    have hi : i.toNat < 5 := i.isLt
    rw [readLimb?_splice_of_disjoint i (.inr (.inr (by rw [h80]; omega))),
      readLimb?_splice_of_disjoint i (.inr (.inr (by rw [h120]; omega))),
      readLimb?_splice_of_disjoint i (.inr (.inr (by rw [h40]; omega)))]

  have Ly : ∀ i : Fin 5,
      readLimb? (a.withOffset 40) i ((((s.mem.splice a oX).splice (a.withOffset 40) oY).splice
        (a.withOffset 120) oZ).splice (a.withOffset 80) oT)
        = readLimb? (a.withOffset 40) i s.mem := by
    intro i
    have hi : i.toNat < 5 := i.isLt
    rw [readLimb?_splice_of_disjoint i (.inr (.inr (by rw [h40, h80]; omega))),
      readLimb?_splice_of_disjoint i (.inr (.inr (by rw [h40, h120]; omega))),
      limbSpliceReadback _ _ _ (fits_splice hc1.1) i]
    have h2 := hcopy₂ i
    rw [limbSpliceReadback _ _ _ hc1u.1 i] at h2
    rw [h2, ← readLimb?_of_equiv heq₁ (a.withOffset 40) i]
    exact readLimb?_splice_of_disjoint i (.inr (.inl (by rw [h40]; omega)))

  have Lz : ∀ i : Fin 5,
      readLimb? (a.withOffset 120) i ((((s.mem.splice a oX).splice (a.withOffset 40) oY).splice
        (a.withOffset 120) oZ).splice (a.withOffset 80) oT)
        = readLimb? (a.withOffset 120) i s.mem := by
    intro i
    have hi : i.toNat < 5 := i.isLt
    rw [readLimb?_splice_of_disjoint i (.inr (.inl (by rw [h80, h120]; omega))),
      limbSpliceReadback _ _ _ (fits_splice (fits_splice hc3.1)) i]
    have h3 := hcopy₃ i
    rw [limbSpliceReadback _ _ _ hc3u.1 i] at h3
    have e2 := readLimb?_of_equiv heq₂ (a.withOffset 120) i
    dsimp only at e2
    rw [readLimb?_splice_of_disjoint i (.inr (.inl (by rw [h40, h120]; omega)))] at e2
    have e1 := readLimb?_of_equiv heq₁ (a.withOffset 120) i
    dsimp only at e1
    rw [readLimb?_splice_of_disjoint i (.inr (.inl (by rw [h120]; omega)))] at e1
    rw [h3, ← e2, ← e1]

  have Lt : ∀ i : Fin 5,
      readLimb? (a.withOffset 80) i ((((s.mem.splice a oX).splice (a.withOffset 40) oY).splice
        (a.withOffset 120) oZ).splice (a.withOffset 80) oT)
        = readLimb? (a.withOffset 80) i (u₃.mem.splice (a.withOffset 80) oT) := by
    intro i
    rw [limbSpliceReadback _ _ _ (fits_splice (fits_splice (fits_splice hc2.1))) i,
      limbSpliceReadback _ _ _ hc2u.1 i]

  refine ⟨oX, oY, oZ, oT, ?equiv, ?point, fun i => ?bx, fun i => ?bt,
    fun i => readLimb_eq_of_readLimb? (Ly i),
    fun i => readLimb_eq_of_readLimb? (Lz i)⟩

  case equiv =>
    have c₂ :=
      GlobalState.Equiv.trans (splice_equiv (p := a.withOffset 40) (x := oY) heq₁) heq₂
    have c₃ :=
      GlobalState.Equiv.trans (splice_equiv (p := a.withOffset 120) (x := oZ) c₂) heq₃
    have hchain :=
      GlobalState.Equiv.trans (splice_equiv (p := a.withOffset 80) (x := oT) c₃) heq₄
    have hu₄WF : u₄.WF := GlobalState.WF.of_equiv hu₃WF.splice heq₄
    have halloc : u₄.alloc = s.alloc :=
      (heq₁.1.trans (heq₂.1.trans (heq₃.1.trans heq₄.1))).symm
    have hglobals : s.globals = u₄.globals :=
      heq₁.globals.trans (heq₂.globals.trans (heq₃.globals.trans heq₄.globals))
    have hpop : (s.popFrame u₄.mem : GlobalState) ≈ u₄ :=
      GlobalState.Equiv.trans
        (killFrom_equiv_of_none (fun b hb => hu₄WF b (by rw [halloc]; omega)))
        ⟨halloc.symm, hglobals, fun _ => rfl⟩
    exact GlobalState.Equiv.trans hchain (GlobalState.Equiv.symm hpop)

  case bx =>
    exact (readLimb_eq_of_readLimb? (h' := isFieldElemPtr_splice hc0)
      (by rw [coordPtr_zero]; exact Lx i)).trans_le (hbndX i)
  case bt =>
    exact (readLimb_eq_of_readLimb? (h' := isFieldElemPtr_splice hc2u) (Lt i)).trans_le (hbndT i)

  case point =>
    have hP : readPoint ha =
        ⟨readFieldElem hc0, readFieldElem hc1, readFieldElem hc3, readFieldElem hc2⟩ :=
      readPoint_eq_of ha rfl rfl rfl rfl
    rw [hP]
    refine readPoint_eq_of _
      (h0 := isFieldElemPtr_splice (isFieldElemPtr_splice (isFieldElemPtr_splice
        (isFieldElemPtr_splice hc0))))
      (h1 := isFieldElemPtr_splice (isFieldElemPtr_splice (isFieldElemPtr_splice
        (isFieldElemPtr_splice hc1))))
      (h2 := isFieldElemPtr_splice (isFieldElemPtr_splice (isFieldElemPtr_splice
        (isFieldElemPtr_splice hc2))))
      (h3 := isFieldElemPtr_splice (isFieldElemPtr_splice (isFieldElemPtr_splice
        (isFieldElemPtr_splice hc3))))
      ?_ ?_ ?_ ?_
    · rw [readFieldElem_eq_of_readLimb (h' := isFieldElemPtr_splice hc0)
        (fun i => readLimb_eq_of_readLimb? (Lx i)), hvalX]
    · exact readFieldElem_eq_of_readLimb (h' := hc1) (fun i => readLimb_eq_of_readLimb? (Ly i))
    · rw [readFieldElem_eq_of_readLimb (h' := isFieldElemPtr_splice hc2u)
        (fun i => readLimb_eq_of_readLimb? (Lt i)), hvalT,
        readFieldElem_eq_of_readLimb (h' := hc2) (fun i => readLimb_eq_of_readLimb? (La i))]
    · exact readFieldElem_eq_of_readLimb (h' := hc3) (fun i => readLimb_eq_of_readLimb? (Lz i))

end Firedancer.Ref

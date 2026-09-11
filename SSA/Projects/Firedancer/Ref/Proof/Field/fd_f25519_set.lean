import SSA.Projects.Firedancer.Ref.Spec.Field.fd_f25519_set
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_set
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Limb

/-!
# `fd_f25519_set` conformance

The region interleaves its loads and stores -- load limb `i` of `q`, store it
to `o`, next limb -- so unlike the fiat regions the loads from limb 1 on run
in an already-spliced state. `o.id ≠ q.id` keeps `q`'s block untouched by
those splices (`getElem?_splice_ne`), which is what lets every load still see
the original limbs.

The intermediate states are introduced as *opaque* variables (`obtain` + a
defining equation) rather than `set`: leaving them as transparent lets makes
the elaborator's final re-check zeta-expand the nested structure updates and
blows the check up from seconds to minutes.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

set_option maxHeartbeats 800000 in
theorem fd_f25519_set_conforms (o q : Pointer) (s : GlobalState)
    (hs : s.WF)
    (hne : o.id ≠ q.id)
    (ho : IsFieldElemPtr s.mem o)
    (hq : IsFieldElemPtr s.mem q) :
    fd_f25519_set_spec o q s hne := by
  simp only [fd_f25519_set_spec, Cfg.denote]

  obtain ⟨qblk, hqblk, hqlen⟩ := id hq.left
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

  denote_expose

  -- what `q`'s block holds at limb `i`, in the gep'd-pointer shape the loads
  -- leave behind; `hq.right` rules out the offset wrapping
  have hlimb : ∀ (i : Fin 5) (d : BitVec 64), d.toNat = 8 * i.toNat →
      qblk.bytes.extractLsb' (q.withOffset d).offsetInBits 64 = outputBV i := by
    rintro i d hd
    have h5 : i.toNat < 5 := i.isLt
    simp only [outputBV, Function.comp_apply]
    exact limbBits hqblk hqinput i (limbOffsetInBits hq.right (k := i.toNat) (by omega) hd)

  -- limb 0: load off the base pointer, store, both still in `s`
  peel_limb 0, q, hq.left, qblk, hqblk, qlimb
  rw [show qlimb₀ = outputBV 0 from by
    rw [hqlimb₀]; exact limbBits hqblk hqinput 0 (by simp)]
  peel_store (outputBV 0), o, ho.left, s
  obtain ⟨s₁, hs₁⟩ : ∃ t : GlobalState, { s with mem := s.mem.splice o (outputBV 0) } = t := ⟨_, rfl⟩
  rw [hs₁]
  have f₁ : Fits s₁.mem o (5 * 64) := hs₁ ▸ fits_splice ho.left
  have fq₁ : Fits s₁.mem q (5 * 64) := hs₁ ▸ fits_splice hq.left

  -- limb 1: `q`'s block is untouched by the store to `o`
  have hqmem₁ : s₁.mem[q.id]? = some (Block.live qblk) := by
    rw [← hs₁, getElem?_splice_ne hne]
    exact hqblk
  peel_gep_limb 1, q, fq₁, s₁, q
  obtain ⟨qb₁, hqb₁, hql₁⟩ := id hq₁
  peel_load (.bitvec (.concrete 64)), qb₁, q₁, hqb₁, s₁
  have hqbeq₁ : qblk = qb₁ := by
    have h := hqb₁
    rw [show (q₁).id = q.id from rfl, hqmem₁] at h
    simpa using h
  subst hqbeq₁
  rw [show qblk.bytes.extractLsb' (q₁).offsetInBits 64 = outputBV 1 from by
    simp only [q₁]
    exact hlimb 1 (8#64) (by simp)]
  peel_gep_limb 1, o, f₁, s₁, o
  peel_store (outputBV 1), o₁, ho₁, s₁
  obtain ⟨s₂, hs₂⟩ : ∃ t : GlobalState, { s₁ with mem := s₁.mem.splice o₁ (outputBV 1) } = t := ⟨_, rfl⟩
  rw [hs₂]
  have f₂ : Fits s₂.mem o (5 * 64) := hs₂ ▸ fits_splice f₁
  have fq₂ : Fits s₂.mem q (5 * 64) := hs₂ ▸ fits_splice fq₁

  -- limb 2: `q`'s block is untouched by the stores to `o`
  have hqmem₂ : s₂.mem[q.id]? = some (Block.live qblk) := by
    rw [← hs₂, getElem?_splice_ne (show (o₁).id ≠ q.id from hne)]
    exact hqmem₁
  peel_gep_limb 2, q, fq₂, s₂, q
  obtain ⟨qb₂, hqb₂, hql₂⟩ := id hq₂
  peel_load (.bitvec (.concrete 64)), qb₂, q₂, hqb₂, s₂
  have hqbeq₂ : qblk = qb₂ := by
    have h := hqb₂
    rw [show (q₂).id = q.id from rfl, hqmem₂] at h
    simpa using h
  subst hqbeq₂
  rw [show qblk.bytes.extractLsb' (q₂).offsetInBits 64 = outputBV 2 from by
    simp only [q₂]
    exact hlimb 2 (16#64) (by simp)]
  peel_gep_limb 2, o, f₂, s₂, o
  peel_store (outputBV 2), o₂, ho₂, s₂
  obtain ⟨s₃, hs₃⟩ : ∃ t : GlobalState, { s₂ with mem := s₂.mem.splice o₂ (outputBV 2) } = t := ⟨_, rfl⟩
  rw [hs₃]
  have f₃ : Fits s₃.mem o (5 * 64) := hs₃ ▸ fits_splice f₂
  have fq₃ : Fits s₃.mem q (5 * 64) := hs₃ ▸ fits_splice fq₂

  -- limb 3: `q`'s block is untouched by the stores to `o`
  have hqmem₃ : s₃.mem[q.id]? = some (Block.live qblk) := by
    rw [← hs₃, getElem?_splice_ne (show (o₂).id ≠ q.id from hne)]
    exact hqmem₂
  peel_gep_limb 3, q, fq₃, s₃, q
  obtain ⟨qb₃, hqb₃, hql₃⟩ := id hq₃
  peel_load (.bitvec (.concrete 64)), qb₃, q₃, hqb₃, s₃
  have hqbeq₃ : qblk = qb₃ := by
    have h := hqb₃
    rw [show (q₃).id = q.id from rfl, hqmem₃] at h
    simpa using h
  subst hqbeq₃
  rw [show qblk.bytes.extractLsb' (q₃).offsetInBits 64 = outputBV 3 from by
    simp only [q₃]
    exact hlimb 3 (24#64) (by simp)]
  peel_gep_limb 3, o, f₃, s₃, o
  peel_store (outputBV 3), o₃, ho₃, s₃
  obtain ⟨s₄, hs₄⟩ : ∃ t : GlobalState, { s₃ with mem := s₃.mem.splice o₃ (outputBV 3) } = t := ⟨_, rfl⟩
  rw [hs₄]
  have f₄ : Fits s₄.mem o (5 * 64) := hs₄ ▸ fits_splice f₃
  have fq₄ : Fits s₄.mem q (5 * 64) := hs₄ ▸ fits_splice fq₃

  -- limb 4: `q`'s block is untouched by the stores to `o`
  have hqmem₄ : s₄.mem[q.id]? = some (Block.live qblk) := by
    rw [← hs₄, getElem?_splice_ne (show (o₃).id ≠ q.id from hne)]
    exact hqmem₃
  peel_gep_limb 4, q, fq₄, s₄, q
  obtain ⟨qb₄, hqb₄, hql₄⟩ := id hq₄
  peel_load (.bitvec (.concrete 64)), qb₄, q₄, hqb₄, s₄
  have hqbeq₄ : qblk = qb₄ := by
    have h := hqb₄
    rw [show (q₄).id = q.id from rfl, hqmem₄] at h
    simpa using h
  subst hqbeq₄
  rw [show qblk.bytes.extractLsb' (q₄).offsetInBits 64 = outputBV 4 from by
    simp only [q₄]
    exact hlimb 4 (32#64) (by simp)]
  peel_gep_limb 4, o, f₄, s₄, o
  peel_store (outputBV 4), o₄, ho₄, s₄
  obtain ⟨s₅, hs₅⟩ : ∃ t : GlobalState, { s₄ with mem := s₄.mem.splice o₄ (outputBV 4) } = t := ⟨_, rfl⟩
  rw [hs₅]
  have f₅ : Fits s₅.mem o (5 * 64) := hs₅ ▸ fits_splice f₄
  have fq₅ : Fits s₅.mem q (5 * 64) := hs₅ ▸ fits_splice fq₄

  simp only [BlockCom.denote_term, Terminator.denote_ret, houtMem,
    ← hs₁, ← hs₂, ← hs₃, ← hs₄, ← hs₅, o₁, o₂, o₃, o₄, simp_denote, simp_sllvm]

end Firedancer.Ref

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Spec.Field.fd_f25519_abs
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_neg
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_sgn
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_if

/-!
# `fd_f25519_abs` conforms to its spec

One 40-byte local and three calls: `neg` fills the local with `-a`, `sgn`
reads `a`'s parity without touching memory, and `if` copies the winner
through the out-parameter. Nothing else writes a block the caller can see,
so the ending is `popFrame_equiv_splice` against that single write.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- A field element survives any step that leaves its block alone: one `live?`
equation carries the pointer, the value and the limb bounds together. -/
private theorem carry_of_live?_eq {m m' : MemoryState} {q : Pointer} {n : ℕ}
    (h : m'.live? q.id = m.live? q.id) (hq : IsFieldElemPtr m q)
    (hb : ∀ (i : Fin 5) (l : ℕ), readLimb? q i m = some l → l ≤ n) :
    ∃ hq' : IsFieldElemPtr m' q,
      readFieldElem hq' = readFieldElem hq
      ∧ ∀ (i : Fin 5) (l : ℕ), readLimb? q i m' = some l → l ≤ n :=
  ⟨isFieldElemPtr_of_live?_eq h hq,
   readFieldElem_eq_of ((readFieldElem?_of_live?_eq h).trans (Option.some_get _).symm),
   limbBounds_of_live?_eq h hb⟩

/-- A splice reads back what it wrote and nothing of the block underneath, so
the same write at `q` is the same field element in any state that fits one
there. -/
private theorem readFieldElem_splice_congr {m m' : MemoryState} {q : Pointer}
    (h : IsFieldElemPtr m q) (h' : IsFieldElemPtr m' q) (x : BitVec (5 * 64)) :
    readFieldElem (m := m.splice q x) (isFieldElemPtr_splice h)
      = readFieldElem (m := m'.splice q x) (isFieldElemPtr_splice h') :=
  (readFieldElem_eq_of (readFieldElem?_splice x h.left)).trans
    (readFieldElem_eq_of (readFieldElem?_splice x h'.left)).symm

/-- The states the walk passes through are numbered by the step that made
them: `s₁` after the `alloca`, `s₂` after `neg`, `s₃` after `sgn`, `s₄` after
`if`; a pointer, value or bound fact carries the index of the state it holds
in. -/
theorem fd_f25519_abs_conforms (o a : Pointer) (s : GlobalState)
    (hs : s.WF)
    (ho : IsFieldElemPtr s.mem o)
    (ha : IsFieldElemPtr s.mem a)
    (halimb : LimbBounds ha) :
    fd_f25519_abs_spec o a s ho ha := by
  simp only [fd_f25519_abs_spec, Cfg.denote]
  have hba : ∀ (i : Fin 5) (l : ℕ), readLimb? a i s.mem = some l → l ≤ 0x8000000000000 :=
    limbBounds_readLimb? ha halimb

  -- `fd_f25519_t t[1]`, the only block the frame holds
  obtain ⟨t, s₁, htdef, hs₁def, hs₁WF, htfits, htid, htoff, -, -⟩ :=
    GlobalState.exists_afterAlloca_facts s hs (5 * 64)
  have fb : FrameBelow s.alloc.nextFreeBlock s s₁ :=
    hs₁def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
  have hno : o.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs ho.left
  have hna : a.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs ha.left
  have hta : t.id ≠ a.id := fun h => by rw [h] at htid; omega
  have hto : t.id ≠ o.id := fun h => by rw [h] at htid; omega
  have pt₁ : IsFieldElemPtr s₁.mem t := ⟨htfits, by simp [htoff]⟩
  obtain ⟨pa₁, hva₁, hba₁⟩ := carry_of_live?_eq (fb a.id hna) ha hba

  -- `fd_f25519_neg( t, a )`: the local takes `-a` at the opp bias bound
  obtain ⟨negOut, hnegval, hnegbnd, s₂, hrun₁, heq₁⟩ :=
    fd_f25519_neg_conforms t a s₁ hs₁WF pt₁ pa₁ (limbBounds_of_readLimb? pa₁ hba₁).bias
  have hs₂WF : s₂.WF := GlobalState.WF.of_equiv hs₁WF.splice heq₁
  have hlive₁ : ∀ b : BlockId, t.id ≠ b → s₂.mem.live? b = s₁.mem.live? b :=
    fun b hb => (heq₁.live b).symm.trans (live?_splice_ne hb)
  have pt₂ : IsFieldElemPtr s₂.mem t :=
    ⟨fits_equiv heq₁ (by simpa using fits_splice pt₁.left), pt₁.right⟩
  have hvt₂ : readFieldElem pt₂ = -readFieldElem ha :=
    readFieldElem_eq_of (by
      rw [← readFieldElem?_of_equiv heq₁ t, ← hva₁, ← hnegval]
      exact (Option.some_get _).symm)
  have hbt₂ : ∀ (i : Fin 5) (l : ℕ), readLimb? t i s₂.mem = some l → l ≤ biasLimb i :=
    fun i l hl => biasBounds_readLimb? _ hnegbnd i l ((readLimb?_of_equiv heq₁ t i).trans hl)
  obtain ⟨pa₂, hva₂', hba₂⟩ := carry_of_live?_eq (hlive₁ a.id hta) pa₁ hba₁
  have hva₂ : readFieldElem pa₂ = readFieldElem ha := hva₂'.trans hva₁

  -- `fd_f25519_sgn( a )`: a read, so the memory comes back unchanged
  obtain ⟨s₃, hrun₂, heq₂⟩ :=
    fd_f25519_sgn_conforms a s₂ hs₂WF pa₂ (limbBounds_of_readLimb? pa₂ hba₂).bias
      (limbSum_lt_of_limbBounds (limbBounds_of_readLimb? pa₂ hba₂))
  have hs₃WF : s₃.WF := GlobalState.WF.of_equiv hs₂WF heq₂
  have hlive₂ : ∀ b : BlockId, s₃.mem.live? b = s₂.mem.live? b := fun b => (heq₂.live b).symm

  -- nothing so far touched a block the caller can see
  have hframe : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → s₃.mem.live? b = s.mem.live? b :=
    fun b hb => (hlive₂ b).trans
      ((hlive₁ b (fun h => by rw [← h] at hb; omega)).trans (fb b hb))
  have po₃ : IsFieldElemPtr s₃.mem o := isFieldElemPtr_of_live?_eq (hframe o.id hno) ho
  obtain ⟨pa₃, hva₃, hba₃⟩ := carry_of_live?_eq (hframe a.id hna) ha hba
  have pt₃ : IsFieldElemPtr s₃.mem t := isFieldElemPtr_of_live?_eq (hlive₂ t.id) pt₂
  have hvt₃' : readFieldElem pt₃ = readFieldElem pt₂ :=
    readFieldElem_eq_of
      ((readFieldElem?_of_live?_eq (hlive₂ t.id)).trans (Option.some_get _).symm)
  have hbt₃ : ∀ (i : Fin 5) (l : ℕ), readLimb? t i s₃.mem = some l → l ≤ biasLimb i :=
    fun i l hl => hbt₂ i l ((readLimb?_of_live?_eq (hlive₂ t.id) i).symm.trans hl)
  have hvt₃ : readFieldElem pt₃ = -readFieldElem ha := hvt₃'.trans hvt₂

  -- `sgn` reaches `selectznz` truncated, so only its low byte decides -- and
  -- that byte is the parity of `a`'s canonical form
  have hbranch : (BitVec.ofNat 32 ((readFieldElem pa₂).val % 2)).setWidth 8 ≠ 0
      ↔ (readFieldElem ha).val % 2 = 1 := by
    rw [hva₂]
    rcases Nat.mod_two_eq_zero_or_one (readFieldElem ha).val with h | h <;> rw [h] <;> decide

  -- `fd_f25519_if( o, sgn, t, a )`, the one caller-visible write
  have hif := fd_f25519_if_conforms o (BitVec.ofNat 32 ((readFieldElem pa₂).val % 2))
    t a s₃ hs₃WF po₃ pt₃ pa₃
  simp only [fd_f25519_if_spec, hbranch] at hif
  obtain ⟨hifval, s₄, hrun₃, heq₃⟩ := hif

  -- the operand it copied out; either way the limbs sit at the opp bound
  set src : Pointer := if (readFieldElem ha).val % 2 = 1 then t else a with hsrcdef
  have hsrc : IsFieldElemPtr s₃.mem src := by rw [hsrcdef]; split <;> assumption
  have hbsrc : ∀ (i : Fin 5) (l : ℕ),
      readLimb? src i s₃.mem = some l → l ≤ biasLimb i := by
    rw [hsrcdef]; split
    · exact hbt₃
    · exact fun i l hl => le_trans (hba₃ i l hl) (tight_le_biasLimb i)

  refine ⟨fun i => (readLimb i hsrc : BitVec 64), ?val, ?bnd, ?sum, ?run⟩

  case val => rw [readFieldElem_splice_congr ho po₃, hifval, hvt₃, hva₃]

  case bnd =>
    refine biasBounds_of_readLimb? _ fun i l hl => ?_
    rw [limbReadbackPack _ _ _ ho.left i, Option.some.injEq] at hl
    subst hl
    simp only [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
    exact le_trans (Nat.mod_le _ _) (hbsrc i _ (Option.some_get _).symm)

  case sum =>
    -- bias bounds give only `≤ 2 · p`, with equality at the all-maximal
    -- vector, whose value is `0`. The negate branch escapes it because `-a`
    -- is non-zero there; the copy branch because `a` is tight.
    by_cases hpar : (readFieldElem ha).val % 2 = 1
    · refine limbSum_lt_of_biasBounds ?bias ?ne
      case bias =>
        refine biasBounds_of_readLimb? _ fun i l hl => ?_
        rw [limbReadbackPack _ _ _ ho.left i, Option.some.injEq] at hl
        subst hl
        simp only [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
        exact le_trans (Nat.mod_le _ _) (hbsrc i _ (Option.some_get _).symm)
      case ne =>
        rw [readFieldElem_splice_congr ho po₃, hifval, hvt₃, hva₃, if_pos hpar]
        refine neg_ne_zero.mpr fun h0 => ?_
        rw [h0] at hpar
        simp at hpar
    · refine limbSum_lt_of_limbBounds (limbBounds_of_readLimb? _ fun i l hl => ?_)
      rw [limbReadbackPack _ _ _ ho.left i, Option.some.injEq] at hl
      subst hl
      simp only [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
      refine le_trans (Nat.mod_le _ _) ?_
      have : src = a := by rw [hsrcdef, if_neg hpar]
      exact hba₃ i _ (this ▸ (Option.some_get _).symm)

  case run =>
    refine ⟨s.popFrame s₄.mem, run_runFunction (s' := s₄) ?walk, ?equiv⟩

    -- the frame held only `t`, so popping it leaves the entry state plus the
    -- write at `o`
    case equiv =>
      exact popFrame_equiv_splice hs hno
        (fun b hb hbo => ((heq₃.live b).symm.trans
          (live?_splice_ne (fun h => hbo h.symm))).trans (hframe b hb))
        ((heq₃.live o.id).symm.trans (live?_splice_congr (hframe o.id hno)))

    case walk =>
      -- %0 = 1
      denote_step_all v 0
      denote_eval v 0 0
      simp only [LLVM.const?] at hv0
      subst hv0
      -- %1 = alloca, then its `lifetime.start`
      peel_alloca from s as s₁ with hs₁def
      rw [← htdef]
      skip_lifetime
      -- %2 = neg(%1, %arg1) ; %3 = sgn(%arg1) ; %4 = if(%arg0, %3, %1, %arg1)
      peel_call hrun₁
      peel_call hrun₂
      peel_call hrun₃
      skip_lifetime
      simp_return

end Firedancer.Ref

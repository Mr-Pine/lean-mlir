/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Ref.Spec.Point.fd_ed25519_partial_dbl
public import SSA.Projects.Firedancer.MLIR.DenoteStep
public import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
public import SSA.Projects.Firedancer.Ref.Proof.Point
public import SSA.Projects.Firedancer.Proof.WriteChain
public import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_add_nr
public import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_sqr4
public import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_add
public import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_sub
public import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_sub_nr

/-!
# `fd_ed25519_partial_dbl` conformance (ref)

Seven calls over five locals `r1..r5`. Every callee result is obtained before
the walk and carried store by store as `readFieldElem?`/`readLimb?` facts, so
the walk itself is only `peel_call`s. `r`'s block after the four stores is
chained through the callees' `≈` by `live?_splice_congr`; every other caller
block is untouched, and the locals die at `popFrame` (`popFrame_equiv_block`).
-/

@[expose] public section

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-! ### Transport through callees

A callee's result is `≈` a few stores; these carry reads at other pointers
through it, and turn its total-read results into `readFieldElem?` facts. -/

/-- `readFieldElem?` from `readFieldElem`. -/
theorem readFieldElem?_eq_some_of {m : MemoryState} {p : Pointer} {h : IsFieldElemPtr m p} {v}
    (hv : readFieldElem h = v) : readFieldElem? p m = some v := by
  rw [← hv]; exact (Option.some_get _).symm

/-- A limb read in a callee's result state is one in the memory it is `≈` to. -/
theorem readLimb?_of_equiv_mem {w s : GlobalState} {m : MemoryState}
    (he : ({ s with mem := m } : GlobalState) ≈ w) (p : Pointer) (i : Fin 5) :
    readLimb? p i w.mem = readLimb? p i m :=
  readLimb?_of_live?_eq (he.live p.id).symm i

/-- ... and passes over the callee's one store, when it is apart from `p`. -/
theorem readLimb?_of_step {w u : GlobalState} {d p : Pointer} {x : BitVec (5 * 64)}
    (he : ({ w with mem := w.mem.splice d x } : GlobalState) ≈ u) (h : FieldApart d p) (i : Fin 5) :
    readLimb? p i u.mem = readLimb? p i w.mem :=
  (readLimb?_of_equiv_mem he p i).trans (readLimb?_splice_of_fieldApart h i)

/-- `readLimb?_of_step` for `fd_f25519_sqr4`'s four stores. -/
theorem readLimb?_of_step4 {w u : GlobalState} {d₁ d₂ d₃ d₄ p : Pointer}
    {x₁ x₂ x₃ x₄ : BitVec (5 * 64)}
    (he :
      ({ w with mem := (((w.mem.splice d₁ x₁).splice d₂ x₂).splice d₃ x₃).splice d₄ x₄ } :
          GlobalState) ≈
        u)
    (h₁ : FieldApart d₁ p) (h₂ : FieldApart d₂ p) (h₃ : FieldApart d₃ p) (h₄ : FieldApart d₄ p)
    (i : Fin 5) : readLimb? p i u.mem = readLimb? p i w.mem :=
  (readLimb?_of_equiv_mem he p i).trans
    ((readLimb?_splice_of_fieldApart h₄ i).trans
      ((readLimb?_splice_of_fieldApart h₃ i).trans
        ((readLimb?_splice_of_fieldApart h₂ i).trans (readLimb?_splice_of_fieldApart h₁ i))))

/-- `isFieldElemPtr_of_step` for four stores. -/
theorem isFieldElemPtr_of_step4 {w u : GlobalState} {d₁ d₂ d₃ d₄ q : Pointer}
    {x₁ x₂ x₃ x₄ : BitVec (5 * 64)}
    (he :
      ({ w with mem := (((w.mem.splice d₁ x₁).splice d₂ x₂).splice d₃ x₃).splice d₄ x₄ } :
          GlobalState) ≈
        u)
    (hq : IsFieldElemPtr w.mem q) : IsFieldElemPtr u.mem q :=
  isFieldElemPtr_of_live?_eq (he.live q.id).symm
    (isFieldElemPtr_splice
      (isFieldElemPtr_splice (isFieldElemPtr_splice (isFieldElemPtr_splice hq))))

/-- `live?_of_step_ne` for four stores. -/
theorem live?_of_step4_ne {w u : GlobalState} {d₁ d₂ d₃ d₄ : Pointer}
    {x₁ x₂ x₃ x₄ : BitVec (5 * 64)}
    (he :
      ({ w with mem := (((w.mem.splice d₁ x₁).splice d₂ x₂).splice d₃ x₃).splice d₄ x₄ } :
          GlobalState) ≈
        u)
    {b : BlockId} (h₁ : d₁.id ≠ b) (h₂ : d₂.id ≠ b) (h₃ : d₃.id ≠ b) (h₄ : d₄.id ≠ b) :
    u.mem.live? b = w.mem.live? b :=
  (he.live b).symm.trans
    ((live?_splice_ne h₄).trans
      ((live?_splice_ne h₃).trans ((live?_splice_ne h₂).trans (live?_splice_ne h₁))))

/-- Equal limb reads are equal field-element reads. -/
theorem readFieldElem?_of_limbs {m m' : MemoryState} {p : Pointer}
    (h : ∀ i, readLimb? p i m' = readLimb? p i m) : readFieldElem? p m' = readFieldElem? p m := by
  simp only [readFieldElem?, h]

/-- ... and carry the limb bounds. -/
theorem bounds_of_limbs {m m' : MemoryState} {p : Pointer} {B : ℕ}
    (h : ∀ i, readLimb? p i m' = readLimb? p i m)
    (hb : ∀ (i : Fin 5) (l : ℕ), readLimb? p i m = some l → l ≤ B) :
    ∀ (i : Fin 5) (l : ℕ), readLimb? p i m' = some l → l ≤ B := fun i l hl =>
  hb i l ((h i).symm.trans hl)

/-- `limbBounds_congr` at any bound. -/
theorem limbBounds_congr_bound {m : MemoryState} {q₁ q₂ : Pointer} {B : ℕ} (hq : q₁ = q₂)
    {h₁ : IsFieldElemPtr m q₁} {h₂ : IsFieldElemPtr m q₂} (hb : LimbBounds h₁ B) :
    LimbBounds h₂ B := by
  subst hq; exact hb

theorem fd_ed25519_partial_dbl_conforms (r a : Pointer) (s : GlobalState) (hs : s.WF)
    (hr : IsPointPtr s.mem r) (ha : IsPointPtr s.mem a) (haX : BiasBounds? a s.mem)
    (haY :
      ∀ (i : Fin 5) (l : ℕ), readLimb? (a.withOffset 40) i s.mem = some l → l ≤ 0x8000000000000)
    (haZ :
      ∀ (i : Fin 5) (l : ℕ), readLimb? (a.withOffset 120) i s.mem = some l → l ≤ 0x18000000000000) :
    fd_ed25519_partial_dbl_spec r a s hr ha := by
  -- the coordinates, in `s`
  have ha0 : IsFieldElemPtr s.mem a := by simpa [Pointer.withOffset] using isCoordPtr ha 0
  have ha1 : IsFieldElemPtr s.mem (a.withOffset 40) := coordPtr_one a ▸ isCoordPtr ha 1
  have ha3 : IsFieldElemPtr s.mem (a.withOffset 120) := coordPtr_three a ▸ isCoordPtr ha 3
  have hr0 : IsFieldElemPtr s.mem r := by simpa [Pointer.withOffset] using isCoordPtr hr 0
  have hr1 : IsFieldElemPtr s.mem (r.withOffset 40) := coordPtr_one r ▸ isCoordPtr hr 1
  have hr2 : IsFieldElemPtr s.mem (r.withOffset 80) := coordPtr_two r ▸ isCoordPtr hr 2
  have hr3 : IsFieldElemPtr s.mem (r.withOffset 120) := coordPtr_three r ▸ isCoordPtr hr 3
  have h40 : (r.withOffset 40).offsetInBits = r.offsetInBits + 320 := by
    simpa using
      withOffset_offsetInBits (off := 40)
        (by
          have := hr.2; simp; omega)
  have h80 : (r.withOffset 80).offsetInBits = r.offsetInBits + 640 := by
    simpa using
      withOffset_offsetInBits (off := 80)
        (by
          have := hr.2; simp; omega)
  have h120 : (r.withOffset 120).offsetInBits = r.offsetInBits + 960 := by
    simpa using
      withOffset_offsetInBits (off := 120)
        (by
          have := hr.2; simp; omega)
  obtain ⟨vX, vY, vZ⟩ := readPoint_coords ha
  obtain ⟨X, hXd⟩ : ∃ X, (readPoint ha).X = X := ⟨_, rfl⟩
  obtain ⟨Y, hYd⟩ : ∃ Y, (readPoint ha).Y = Y := ⟨_, rfl⟩
  obtain ⟨Z, hZd⟩ : ∃ Z, (readPoint ha).Z = Z := ⟨_, rfl⟩
  rw [hXd] at vX
  rw [hYd] at vY
  rw [hZd] at vZ
  -- `fd_f25519_t r1[1], …, r5[1]`
  obtain ⟨l1, s₁, hl1def, hs₁def, hs₁, hfit1, hl1id, hl1off, hctr₁, -⟩ :=
    GlobalState.exists_afterAlloca_facts s hs (5 * 64)
  obtain ⟨l2, s₂, hl2def, hs₂def, hs₂, hfit2, hl2id, hl2off, hctr₂, hfr2⟩ :=
    GlobalState.exists_afterAlloca_facts s₁ hs₁ (5 * 64)
  obtain ⟨l3, s₃, hl3def, hs₃def, hs₃, hfit3, hl3id, hl3off, hctr₃, hfr3⟩ :=
    GlobalState.exists_afterAlloca_facts s₂ hs₂ (5 * 64)
  obtain ⟨l4, s₄, hl4def, hs₄def, hs₄, hfit4, hl4id, hl4off, hctr₄, hfr4⟩ :=
    GlobalState.exists_afterAlloca_facts s₃ hs₃ (5 * 64)
  obtain ⟨l5, s₅, hl5def, hs₅def, hs₅, hfit5, hl5id, hl5off, hctr₅, hfr5⟩ :=
    GlobalState.exists_afterAlloca_facts s₄ hs₄ (5 * 64)
  have ha_lt : a.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs ha.1
  have hr_lt : r.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hr.1
  have ne : ∀ p q : Pointer, p.id.id ≠ q.id.id → p.id ≠ q.id := fun p q h e =>
    h (congrArg BlockId.id e)
  have ap : ∀ p q : Pointer, p.id.id ≠ q.id.id → FieldApart p q := fun p q h => .inl (ne p q h)
  have fb₅ : FrameBelow s.alloc.nextFreeBlock s s₅ := by
    have fb₁ : FrameBelow s.alloc.nextFreeBlock s s₁ :=
      hs₁def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
    have fb₂ : FrameBelow s.alloc.nextFreeBlock s s₂ :=
      hs₂def ▸ FrameBelow.afterAlloca (by omega) fb₁
    have fb₃ : FrameBelow s.alloc.nextFreeBlock s s₃ :=
      hs₃def ▸ FrameBelow.afterAlloca (by omega) fb₂
    have fb₄ : FrameBelow s.alloc.nextFreeBlock s s₄ :=
      hs₄def ▸ FrameBelow.afterAlloca (by omega) fb₃
    exact hs₅def ▸ FrameBelow.afterAlloca (by omega) fb₄
  have hla : s₅.mem.live? a.id = s.mem.live? a.id := fb₅ a.id ha_lt
  have hlr : s₅.mem.live? r.id = s.mem.live? r.id := fb₅ r.id hr_lt
  -- the locals, in `s₅`
  have hl1₅ : IsFieldElemPtr s₅.mem l1 :=
    ⟨fits_of_live?_eq
        ((hfr5 _ (ne l1 l5 (by omega))).trans
          ((hfr4 _ (ne l1 l4 (by omega))).trans
            ((hfr3 _ (ne l1 l3 (by omega))).trans (hfr2 _ (ne l1 l2 (by omega))))))
        hfit1,
      by simp [hl1off]⟩
  have hl2₅ : IsFieldElemPtr s₅.mem l2 :=
    ⟨fits_of_live?_eq
        ((hfr5 _ (ne l2 l5 (by omega))).trans
          ((hfr4 _ (ne l2 l4 (by omega))).trans (hfr3 _ (ne l2 l3 (by omega)))))
        hfit2,
      by simp [hl2off]⟩
  have hl3₅ : IsFieldElemPtr s₅.mem l3 :=
    ⟨fits_of_live?_eq ((hfr5 _ (ne l3 l5 (by omega))).trans (hfr4 _ (ne l3 l4 (by omega)))) hfit3,
      by simp [hl3off]⟩
  have hl4₅ : IsFieldElemPtr s₅.mem l4 :=
    ⟨fits_of_live?_eq (hfr5 _ (ne l4 l5 (by omega))) hfit4, by simp [hl4off]⟩
  have hl5₅ : IsFieldElemPtr s₅.mem l5 := ⟨hfit5, by simp [hl5off]⟩
  -- `a`'s coordinates in `s₅`
  have vX₅ : readFieldElem? a s₅.mem = some X := (readFieldElem?_of_live?_eq (p := a) hla).trans vX
  have vY₅ : readFieldElem? (a.withOffset 40) s₅.mem = some Y :=
    (readFieldElem?_of_live?_eq (p := a.withOffset 40) hla).trans vY
  have vZ₅ : readFieldElem? (a.withOffset 120) s₅.mem = some Z :=
    (readFieldElem?_of_live?_eq (p := a.withOffset 120) hla).trans vZ
  have ha0₅ : IsFieldElemPtr s₅.mem a := isFieldElemPtr_of_live?_eq hla ha0
  have ha1₅ : IsFieldElemPtr s₅.mem (a.withOffset 40) := isFieldElemPtr_of_live?_eq hla ha1
  have ha3₅ : IsFieldElemPtr s₅.mem (a.withOffset 120) := isFieldElemPtr_of_live?_eq hla ha3
  have bX₅ := limbBounds_of_live?_eq (p := a) hla (biasBounds?_le haX)
  have bY₅ := limbBounds_of_live?_eq (p := a.withOffset 40) hla haY
  have bZ₅ := limbBounds_of_live?_eq (p := a.withOffset 120) hla haZ
  -- 1. `fd_f25519_add_nr( r1, a->X, a->Y )`
  obtain ⟨x1, hv1, hb1, u₁, hrun₁, heq₁⟩ :=
    fd_f25519_add_nr_conforms l1 a (a.withOffset 40) s₅ hs₅ bX₅ bY₅ hl1₅ ha0₅ ha1₅
  have hu₁ : u₁.WF := hs₅.splice.of_equiv heq₁
  have vL1 : readFieldElem? l1 u₁.mem = some (X + Y) :=
    (readFieldElem?_of_limbs (readLimb?_of_equiv_mem heq₁ l1)).trans
      (readFieldElem?_eq_some_of
        (hv1.trans (by rw [readFieldElem_eq_of vX₅, readFieldElem_eq_of vY₅])))
  have bL1 := bounds_of_limbs (readLimb?_of_equiv_mem heq₁ l1) (limbBounds_readLimb? _ hb1)
  have la₁ : ∀ p : Pointer, p.id = a.id → ∀ i, readLimb? p i u₁.mem = readLimb? p i s₅.mem :=
    fun p hp i =>
    readLimb?_of_step heq₁
      (ap l1 p
        (by
          rw [hp]; omega))
      i
  have bX₁ := bounds_of_limbs (la₁ a rfl) bX₅
  have bY₁ := bounds_of_limbs (la₁ (a.withOffset 40) rfl) bY₅
  have bZ₁ := bounds_of_limbs (la₁ (a.withOffset 120) rfl) bZ₅
  have vX₁ := (readFieldElem?_of_limbs (la₁ a rfl)).trans vX₅
  have vY₁ := (readFieldElem?_of_limbs (la₁ (a.withOffset 40) rfl)).trans vY₅
  have vZ₁ := (readFieldElem?_of_limbs (la₁ (a.withOffset 120) rfl)).trans vZ₅
  have ha0₁ := isFieldElemPtr_of_step heq₁ ha0₅
  have ha1₁ := isFieldElemPtr_of_step heq₁ ha1₅
  have ha3₁ := isFieldElemPtr_of_step heq₁ ha3₅
  have hl1₁ := isFieldElemPtr_of_step heq₁ hl1₅
  have hl2₁ := isFieldElemPtr_of_step heq₁ hl2₅
  have hl3₁ := isFieldElemPtr_of_step heq₁ hl3₅
  have hl4₁ := isFieldElemPtr_of_step heq₁ hl4₅
  have hl5₁ := isFieldElemPtr_of_step heq₁ hl5₅
  -- 2. `fd_f25519_sqr4( r2, a->X, r3, a->Y, r4, a->Z, r5, r1 )`
  have hdst : [l2, l3, l4, l5].Pairwise FieldApart := by
    refine
        List.pairwise_cons.2
          ⟨?_,
            List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, List.pairwise_singleton _ _⟩⟩⟩ <;>
      intro q hq <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq <;>
      rcases hq with rfl | rfl | rfl <;>
      exact ap _ _ (by omega)
  have hsrc :
    ∀ d ∈ [l2, l3, l4, l5], ∀ x ∈ [a, a.withOffset 40, a.withOffset 120, l1], d.id ≠ x.id := by
    intro d hd x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd hx
    rcases hd with rfl | rfl | rfl | rfl <;> rcases hx with rfl | rfl | rfl | rfl <;>
      exact
        ne _ _
          (by
            first
            | omega
            | (simp only [withOffset_id]; omega))
  have hbounds :
    ∀ x ∈ [a, a.withOffset 40, a.withOffset 120, l1],
      ∀ (i : Fin 5) (l : ℕ), readLimb? x i u₁.mem = some l → l ≤ 0x18000000000000 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact fun i l h => (bX₁ i l h).trans (by norm_num)
    · exact fun i l h => (bY₁ i l h).trans (by norm_num)
    · exact bZ₁
    · exact bL1
  obtain ⟨o2, o3, o4, o5, ⟨u₂, hrun₂, heq₂⟩, hv2, hb2, hv3, hb3, hv4, hb4, hv5, hb5⟩ :=
    fd_f25519_sqr4_conforms l2 a l3 (a.withOffset 40) l4 (a.withOffset 120) l5 l1 u₁ hu₁ hdst hsrc
      hl2₁ ha0₁ hl3₁ ha1₁ hl4₁ ha3₁ hl5₁ hl1₁ hbounds
  have hu₂ : u₂.WF := (wf_splice4 hu₁).of_equiv heq₂
  have vL2 : readFieldElem? l2 u₂.mem = some (X * X) :=
    (readFieldElem?_of_limbs (readLimb?_of_equiv_mem heq₂ l2)).trans
      (readFieldElem?_eq_some_of (hv2.trans (by rw [readFieldElem_eq_of vX₁])))
  have vL3 : readFieldElem? l3 u₂.mem = some (Y * Y) :=
    (readFieldElem?_of_limbs (readLimb?_of_equiv_mem heq₂ l3)).trans
      (readFieldElem?_eq_some_of (hv3.trans (by rw [readFieldElem_eq_of vY₁])))
  have vL4 : readFieldElem? l4 u₂.mem = some (Z * Z) :=
    (readFieldElem?_of_limbs (readLimb?_of_equiv_mem heq₂ l4)).trans
      (readFieldElem?_eq_some_of (hv4.trans (by rw [readFieldElem_eq_of vZ₁])))
  have vL5 : readFieldElem? l5 u₂.mem = some ((X + Y) * (X + Y)) :=
    (readFieldElem?_of_limbs (readLimb?_of_equiv_mem heq₂ l5)).trans
      (readFieldElem?_eq_some_of (hv5.trans (by rw [readFieldElem_eq_of vL1])))
  have bL2 := bounds_of_limbs (readLimb?_of_equiv_mem heq₂ l2) (limbBounds_readLimb? _ hb2)
  have bL3 := bounds_of_limbs (readLimb?_of_equiv_mem heq₂ l3) (limbBounds_readLimb? _ hb3)
  have bL4 := bounds_of_limbs (readLimb?_of_equiv_mem heq₂ l4) (limbBounds_readLimb? _ hb4)
  have bL5 := bounds_of_limbs (readLimb?_of_equiv_mem heq₂ l5) (limbBounds_readLimb? _ hb5)
  have hl2₂ := isFieldElemPtr_of_step4 heq₂ hl2₁
  have hl3₂ := isFieldElemPtr_of_step4 heq₂ hl3₁
  have hl4₂ := isFieldElemPtr_of_step4 heq₂ hl4₁
  have hl5₂ := isFieldElemPtr_of_step4 heq₂ hl5₁
  -- 3. `fd_f25519_add( r4, r4, r4 )`
  obtain ⟨x4, hv4', hb4', u₃, hrun₃, heq₃⟩ :=
    fd_f25519_add_conforms l4 l4 l4 u₂ hu₂ bL4 bL4 hl4₂ hl4₂ hl4₂
  have hu₃ : u₃.WF := hu₂.splice.of_equiv heq₃
  have vL4₃ : readFieldElem? l4 u₃.mem = some (Z * Z + Z * Z) :=
    (readFieldElem?_of_limbs (readLimb?_of_equiv_mem heq₃ l4)).trans
      (readFieldElem?_eq_some_of (hv4'.trans (by rw [readFieldElem_eq_of vL4])))
  have bL4₃ := bounds_of_limbs (readLimb?_of_equiv_mem heq₃ l4) (limbBounds_readLimb? _ hb4')
  have eL2₃ := readLimb?_of_step heq₃ (ap l4 l2 (by omega))
  have eL3₃ := readLimb?_of_step heq₃ (ap l4 l3 (by omega))
  have eL5₃ := readLimb?_of_step heq₃ (ap l4 l5 (by omega))
  have hr2₃ : IsFieldElemPtr u₃.mem (r.withOffset 80) :=
    isFieldElemPtr_of_step heq₃
      (isFieldElemPtr_of_step4 heq₂
        (isFieldElemPtr_of_step heq₁ (isFieldElemPtr_of_live?_eq hlr hr2)))
  have hr3₃ : IsFieldElemPtr u₃.mem (r.withOffset 120) :=
    isFieldElemPtr_of_step heq₃
      (isFieldElemPtr_of_step4 heq₂
        (isFieldElemPtr_of_step heq₁ (isFieldElemPtr_of_live?_eq hlr hr3)))
  have hr1₃ : IsFieldElemPtr u₃.mem (r.withOffset 40) :=
    isFieldElemPtr_of_step heq₃
      (isFieldElemPtr_of_step4 heq₂
        (isFieldElemPtr_of_step heq₁ (isFieldElemPtr_of_live?_eq hlr hr1)))
  have hr0₃ : IsFieldElemPtr u₃.mem r :=
    isFieldElemPtr_of_step heq₃
      (isFieldElemPtr_of_step4 heq₂
        (isFieldElemPtr_of_step heq₁ (isFieldElemPtr_of_live?_eq hlr hr0)))
  -- 4. `fd_f25519_add( r->T, r2, r3 )`
  obtain ⟨xT, hvT, hbT, u₄, hrun₄, heq₄⟩ :=
    fd_f25519_add_conforms (r.withOffset 80) l2 l3 u₃ hu₃ (bounds_of_limbs eL2₃ bL2)
      (bounds_of_limbs eL3₃ bL3) hr2₃ (isFieldElemPtr_of_step heq₃ hl2₂)
      (isFieldElemPtr_of_step heq₃ hl3₂)
  have hu₄ : u₄.WF := hu₃.splice.of_equiv heq₄
  have vT₄ :
    readFieldElem? (r.withOffset 80) (u₃.mem.splice (r.withOffset 80) (packLimbs xT)) =
      some (X * X + Y * Y) :=
    readFieldElem?_eq_some_of
      (hvT.trans
        (by
          rw [readFieldElem_eq_of ((readFieldElem?_of_limbs eL2₃).trans vL2),
            readFieldElem_eq_of ((readFieldElem?_of_limbs eL3₃).trans vL3)]))
  have eL2₄ :=
    readLimb?_of_step heq₄
      (ap (r.withOffset 80) l2
        (by
          simp only [withOffset_id]; omega))
  have eL3₄ :=
    readLimb?_of_step heq₄
      (ap (r.withOffset 80) l3
        (by
          simp only [withOffset_id]; omega))
  have eL4₄ :=
    readLimb?_of_step heq₄
      (ap (r.withOffset 80) l4
        (by
          simp only [withOffset_id]; omega))
  have eL5₄ :=
    readLimb?_of_step heq₄
      (ap (r.withOffset 80) l5
        (by
          simp only [withOffset_id]; omega))
  -- 5. `fd_f25519_sub( r->Z, r2, r3 )`
  obtain ⟨xZ, hvZ, hbZ, u₅, hrun₅, heq₅⟩ :=
    fd_f25519_sub_conforms (r.withOffset 120) l2 l3 u₄ hu₄
      (bounds_of_limbs eL2₄ (bounds_of_limbs eL2₃ bL2))
      (biasBounds?_of_limbBounds (bounds_of_limbs eL3₄ (bounds_of_limbs eL3₃ bL3)))
      (isFieldElemPtr_of_step heq₄ hr3₃)
      (isFieldElemPtr_of_step heq₄ (isFieldElemPtr_of_step heq₃ hl2₂))
      (isFieldElemPtr_of_step heq₄ (isFieldElemPtr_of_step heq₃ hl3₂))
  have hu₅ : u₅.WF := hu₄.splice.of_equiv heq₅
  have vZ₅' :
    readFieldElem? (r.withOffset 120) (u₄.mem.splice (r.withOffset 120) xZ) =
      some (X * X - Y * Y) :=
    readFieldElem?_eq_some_of
      (hvZ.trans
        (by
          rw [readFieldElem_eq_of
              ((readFieldElem?_of_limbs eL2₄).trans ((readFieldElem?_of_limbs eL2₃).trans vL2)),
            readFieldElem_eq_of
              ((readFieldElem?_of_limbs eL3₄).trans ((readFieldElem?_of_limbs eL3₃).trans vL3))]))
  have bZ₅' := bounds_of_limbs (readLimb?_of_equiv_mem heq₅ _) (limbBounds_readLimb? _ hbZ)
  have eL4₅ :=
    readLimb?_of_step heq₅
      (ap (r.withOffset 120) l4
        (by
          simp only [withOffset_id]; omega))
  have eL5₅ :=
    readLimb?_of_step heq₅
      (ap (r.withOffset 120) l5
        (by
          simp only [withOffset_id]; omega))
  have eT₅ := readLimb?_of_step heq₅ (p := r.withOffset 80) (.inr (.inr (by omega)))
  -- 6. `fd_f25519_add_nr( r->Y, r4, r->Z )`
  obtain ⟨xY, hvY, hbY, u₆, hrun₆, heq₆⟩ :=
    fd_f25519_add_nr_conforms (r.withOffset 40) l4 (r.withOffset 120) u₅ hu₅
      (bounds_of_limbs eL4₅ (bounds_of_limbs eL4₄ bL4₃)) bZ₅'
      (isFieldElemPtr_of_step heq₅ (isFieldElemPtr_of_step heq₄ hr1₃))
      (isFieldElemPtr_of_step heq₅ (isFieldElemPtr_of_step heq₄ (isFieldElemPtr_of_step heq₃ hl4₂)))
      (isFieldElemPtr_of_step heq₅ (isFieldElemPtr_of_step heq₄ hr3₃))
  have hu₆ : u₆.WF := hu₅.splice.of_equiv heq₆
  have vY₆ :
    readFieldElem? (r.withOffset 40) (u₅.mem.splice (r.withOffset 40) (packLimbs xY)) =
      some ((Z * Z + Z * Z) + (X * X - Y * Y)) :=
    readFieldElem?_eq_some_of
      (hvY.trans
        (by
          rw [readFieldElem_eq_of
              ((readFieldElem?_of_limbs eL4₅).trans ((readFieldElem?_of_limbs eL4₄).trans vL4₃)),
            readFieldElem_eq_of
              ((readFieldElem?_of_limbs (readLimb?_of_equiv_mem heq₅ _)).trans vZ₅')]))
  have eT₆ := readLimb?_of_step heq₆ (p := r.withOffset 80) (.inr (.inl (by omega)))
  have eL5₆ :=
    readLimb?_of_step heq₆
      (ap (r.withOffset 40) l5
        (by
          simp only [withOffset_id]; omega))
  -- 7. `fd_f25519_sub_nr( r->X, r->T, r5 )`
  have eT :
    ∀ i,
      readLimb? (r.withOffset 80) i u₆.mem =
        readLimb? (r.withOffset 80) i (u₃.mem.splice (r.withOffset 80) (packLimbs xT)) :=
    fun i => (eT₆ i).trans ((eT₅ i).trans (readLimb?_of_equiv_mem heq₄ _ i))
  have eL5 : ∀ i, readLimb? l5 i u₆.mem = readLimb? l5 i u₂.mem := fun i =>
    (eL5₆ i).trans ((eL5₅ i).trans ((eL5₄ i).trans (eL5₃ i)))
  have hr0₆ :=
    isFieldElemPtr_of_step heq₆ (isFieldElemPtr_of_step heq₅ (isFieldElemPtr_of_step heq₄ hr0₃))
  obtain ⟨xX, hvX, hbX, u₇, hrun₇, heq₇⟩ :=
    fd_f25519_sub_nr_conforms r (r.withOffset 80) l5 u₆ hu₆
      (bounds_of_limbs eT (limbBounds_readLimb? _ hbT))
      (biasBounds?_of_limbBounds (bounds_of_limbs eL5 bL5)) hr0₆
      (isFieldElemPtr_of_step heq₆ (isFieldElemPtr_of_step heq₅ (isFieldElemPtr_of_step heq₄ hr2₃)))
      (isFieldElemPtr_of_step heq₆
        (isFieldElemPtr_of_step heq₅
          (isFieldElemPtr_of_step heq₄ (isFieldElemPtr_of_step heq₃ hl5₂))))
  have vX₇ : readFieldElem? r (u₆.mem.splice r xX) = some ((X * X + Y * Y) - (X + Y) * (X + Y)) :=
    readFieldElem?_eq_some_of
      (hvX.trans
        (by
          rw [readFieldElem_eq_of ((readFieldElem?_of_limbs eT).trans vT₄),
            readFieldElem_eq_of ((readFieldElem?_of_limbs eL5).trans vL5)]))
  -- the four coordinates, read back in the spec's memory
  obtain ⟨M, hM⟩ :
    ∃ M : MemoryState,
      M =
        (((s.mem.splice (r.withOffset 80) (packLimbs xT)).splice (r.withOffset 120) xZ).splice
              (r.withOffset 40) (packLimbs xY)).splice
          r xX :=
    ⟨_, rfl⟩
  have eX : ∀ i, readLimb? r i M = readLimb? r i (u₆.mem.splice r xX) := fun i => by
    rw [hM]
    exact readLimb?_splice_self_congr xX (fits_splice (fits_splice (fits_splice hr0.1))) hr0₆.1 i
  have eY :
    ∀ i,
      readLimb? (r.withOffset 40) i M =
        readLimb? (r.withOffset 40) i (u₅.mem.splice (r.withOffset 40) (packLimbs xY)) :=
    fun i => by
    rw [hM]
    exact
      (readLimb?_splice_of_fieldApart (.inr (.inl (by omega))) i).trans
        (readLimb?_splice_self_congr _ (fits_splice (fits_splice hr1.1))
          (isFieldElemPtr_of_step heq₅ (isFieldElemPtr_of_step heq₄ hr1₃)).1 i)
  have eZ :
    ∀ i,
      readLimb? (r.withOffset 120) i M =
        readLimb? (r.withOffset 120) i (u₄.mem.splice (r.withOffset 120) xZ) :=
    fun i => by
    rw [hM]
    exact
      (readLimb?_splice_of_fieldApart (.inr (.inl (by omega))) i).trans
        ((readLimb?_splice_of_fieldApart (.inr (.inl (by omega))) i).trans
          (readLimb?_splice_self_congr _ (fits_splice hr3.1) (isFieldElemPtr_of_step heq₄ hr3₃).1
            i))
  have eT' :
    ∀ i,
      readLimb? (r.withOffset 80) i M =
        readLimb? (r.withOffset 80) i (u₃.mem.splice (r.withOffset 80) (packLimbs xT)) :=
    fun i => by
    rw [hM]
    exact
      (readLimb?_splice_of_fieldApart (.inr (.inl (by omega))) i).trans
        ((readLimb?_splice_of_fieldApart (.inr (.inl (by omega))) i).trans
          ((readLimb?_splice_of_fieldApart (.inr (.inr (by omega))) i).trans
            (readLimb?_splice_self_congr _ hr2.1 hr2₃.1 i)))
  have hoX : IsFieldElemPtr M r := by
    rw [hM];
    exact
      isFieldElemPtr_splice
        (isFieldElemPtr_splice (isFieldElemPtr_splice (isFieldElemPtr_splice hr0)))
  have hoY : IsFieldElemPtr M (r.withOffset 40) := by
    rw [hM];
    exact
      isFieldElemPtr_splice
        (isFieldElemPtr_splice (isFieldElemPtr_splice (isFieldElemPtr_splice hr1)))
  have hoT : IsFieldElemPtr M (r.withOffset 80) := by
    rw [hM];
    exact
      isFieldElemPtr_splice
        (isFieldElemPtr_splice (isFieldElemPtr_splice (isFieldElemPtr_splice hr2)))
  have hoZ : IsFieldElemPtr M (r.withOffset 120) := by
    rw [hM];
    exact
      isFieldElemPtr_splice
        (isFieldElemPtr_splice (isFieldElemPtr_splice (isFieldElemPtr_splice hr3)))
  have rX : readFieldElem hoX = (X * X + Y * Y) - (X + Y) * (X + Y) :=
    readFieldElem_eq_of ((readFieldElem?_of_limbs eX).trans vX₇)
  have rY : readFieldElem hoY = (Z * Z + Z * Z) + (X * X - Y * Y) :=
    readFieldElem_eq_of ((readFieldElem?_of_limbs eY).trans vY₆)
  have rT : readFieldElem hoT = X * X + Y * Y :=
    readFieldElem_eq_of ((readFieldElem?_of_limbs eT').trans vT₄)
  have rZ : readFieldElem hoZ = X * X - Y * Y :=
    readFieldElem_eq_of ((readFieldElem?_of_limbs eZ).trans vZ₅')
  have cX : LimbBounds hoX 0x18000000000000 :=
    limbBounds_of_readLimb? hoX (bounds_of_limbs eX (limbBounds_readLimb? _ hbX))
  have cY : LimbBounds hoY 0x18000000000000 :=
    limbBounds_of_readLimb? hoY (bounds_of_limbs eY (limbBounds_readLimb? _ hbY))
  have cT : LimbBounds hoT :=
    limbBounds_of_readLimb? hoT (bounds_of_limbs eT' (limbBounds_readLimb? _ hbT))
  have cZ : LimbBounds hoZ :=
    limbBounds_of_readLimb? hoZ (bounds_of_limbs eZ (limbBounds_readLimb? _ hbZ))
  -- the frame: every caller block but `r` as in `s`, and `r` as the four stores left it
  have nl :
    ∀ (p : Pointer) (b : BlockId),
      s.alloc.nextFreeBlock ≤ p.id.id → b.id < s.alloc.nextFreeBlock → p.id ≠ b :=
    fun p b hp hb h => by
    have := congrArg BlockId.id h; omega
  have hfm :
    ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → b ≠ r.id → u₇.mem.live? b = s.mem.live? b :=
    fun b hb hbr =>
    have hrb : r.id ≠ b := fun h => hbr h.symm
    (live?_of_step_ne heq₇ hrb).trans
      ((live?_of_step_ne heq₆ hrb).trans
        ((live?_of_step_ne heq₅ hrb).trans
          ((live?_of_step_ne heq₄ hrb).trans
            ((live?_of_step_ne heq₃ (nl l4 b (by omega) hb)).trans
              ((live?_of_step4_ne heq₂ (nl l2 b (by omega) hb) (nl l3 b (by omega) hb)
                    (nl l4 b (by omega) hb) (nl l5 b (by omega) hb)).trans
                ((live?_of_step_ne heq₁ (nl l1 b (by omega) hb)).trans (fb₅ b hb)))))))
  have hfn : ∀ b : BlockId, b ≠ r.id → M.live? b = s.mem.live? b := fun b hbr => by
    have hrb : r.id ≠ b := fun h => hbr h.symm
    rw [hM]
    exact
      (live?_splice_ne (p := r) hrb).trans
        ((live?_splice_ne (p := r.withOffset 40) hrb).trans
          ((live?_splice_ne (p := r.withOffset 120) hrb).trans
            (live?_splice_ne (p := r.withOffset 80) hrb)))
  have k3 : u₃.mem.live? r.id = s.mem.live? r.id :=
    (live?_of_step_ne heq₃ (nl l4 r.id (by omega) hr_lt)).trans
      ((live?_of_step4_ne heq₂ (nl l2 r.id (by omega) hr_lt) (nl l3 r.id (by omega) hr_lt)
            (nl l4 r.id (by omega) hr_lt) (nl l5 r.id (by omega) hr_lt)).trans
        ((live?_of_step_ne heq₁ (nl l1 r.id (by omega) hr_lt)).trans hlr))
  have k4 :=
    (live?_of_equiv_mem heq₄.symm r.id).trans
      (live?_splice_congr (p := r.withOffset 80) (x := packLimbs xT) k3)
  have k5 :=
    (live?_of_equiv_mem heq₅.symm r.id).trans
      (live?_splice_congr (p := r.withOffset 120) (x := xZ) k4)
  have k6 :=
    (live?_of_equiv_mem heq₆.symm r.id).trans
      (live?_splice_congr (p := r.withOffset 40) (x := packLimbs xY) k5)
  have k7 : u₇.mem.live? r.id = M.live? r.id := by
    rw [hM]
    exact (live?_of_equiv_mem heq₇.symm r.id).trans (live?_splice_congr (p := r) (x := xX) k6)
  have hpop := popFrame_equiv_block hs hr_lt hfm hfn k7
  subst hM
  refine
    ⟨packLimbs xT, xZ, packLimbs xY, xX,
      ⟨s.popFrame u₇.mem, run_runFunction (s' := u₇) ?run, GlobalState.Equiv.symm hpop⟩, ?val,
      limbBounds_congr_bound (by simp [Pointer.withOffset]) cX,
      limbBounds_congr_bound (coordPtr_one r).symm cY, limbBounds_congr (coordPtr_two r).symm cT,
      limbBounds_congr (coordPtr_three r).symm cZ⟩
  case val =>
    rw [readPoint_eq_of _ rX rY rT rZ]
    simp only [Point.partialDbl, hXd, hYd, hZd, Point.mk.injEq]
    refine ⟨by ring, by ring, by ring, by ring⟩
  case run =>
    simp only [Cfg.denote]
    denote_step_all v 0
    denote_eval v 0 0
    simp only [LLVM.const?] at hv0
    subst hv0
    peel_alloca from s as s₁ with hs₁def
    peel_alloca from s₁ as s₂ with hs₂def
    peel_alloca from s₂ as s₃ with hs₃def
    peel_alloca from s₃ as s₄ with hs₄def
    peel_alloca from s₄ as s₅ with hs₅def
    rw [← hl1def, ← hl2def, ← hl3def, ← hl4def, ← hl5def]
    peel_lifetime
    peel_lifetime
    peel_lifetime
    peel_lifetime
    peel_lifetime
    denote_step_reduce v 6 [gepConst, ptradd, LLVM.const?]
    have e6 : v6 = .value (a.withOffset 40) := by simp [hv6, Pointer.withOffset, simp_sllvm]
    subst e6
    clear hv6
    refine
      (BlockCom.run_bind_denote_call_of_value (x := PoisonOr.value (l1)) (s' := u₁) ?_).trans ?_
    · exact hrun₁
    denote_step_reduce v 8 [gepConst, ptradd, LLVM.const?]
    have e8 : v8 = .value (a.withOffset 120) := by simp [hv8, Pointer.withOffset, simp_sllvm]
    subst e8
    clear hv8
    refine (BlockCom.run_bind_denote_call_of_nil (s' := u₂) ?_).trans ?_
    · exact hrun₂
    refine
      (BlockCom.run_bind_denote_call_of_value (x := PoisonOr.value (l4)) (s' := u₃) ?_).trans ?_
    · exact hrun₃
    denote_step_reduce v 10 [gepConst, ptradd, LLVM.const?]
    have e10 : v10 = .value (r.withOffset 80) := by simp [hv10, Pointer.withOffset, simp_sllvm]
    subst e10
    clear hv10
    refine
      (BlockCom.run_bind_denote_call_of_value (x := PoisonOr.value (r.withOffset 80)) (s' := u₄)
            ?_).trans
        ?_
    · exact hrun₄
    denote_step_reduce v 12 [gepConst, ptradd, LLVM.const?]
    have e12 : v12 = .value (r.withOffset 120) := by simp [hv12, Pointer.withOffset, simp_sllvm]
    subst e12
    clear hv12
    refine
      (BlockCom.run_bind_denote_call_of_value (x := PoisonOr.value (r.withOffset 120)) (s' := u₅)
            ?_).trans
        ?_
    · exact hrun₅
    denote_step_reduce v 14 [gepConst, ptradd, LLVM.const?]
    have e14 : v14 = .value (r.withOffset 40) := by simp [hv14, Pointer.withOffset, simp_sllvm]
    subst e14
    clear hv14
    refine
      (BlockCom.run_bind_denote_call_of_value (x := PoisonOr.value (r.withOffset 40)) (s' := u₆)
            ?_).trans
        ?_
    · exact hrun₆
    refine (BlockCom.run_bind_denote_call_of_value (x := PoisonOr.value (r)) (s' := u₇) ?_).trans ?_
    · exact hrun₇
    peel_lifetime
    peel_lifetime
    peel_lifetime
    peel_lifetime
    peel_lifetime
    rfl

end Firedancer.Ref

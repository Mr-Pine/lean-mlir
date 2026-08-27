import Mathlib.Data.Fin.VecNotation
import SSA.Projects.Firedancer.Curve
import SSA.Projects.Firedancer.Ed25519
import SSA.Projects.SLLVM.Dialect

namespace Firedancer.Ref
open LeanMLIR SLLVM

def decodeFieldElem (limbs: Fin 5 → ℕ) :=
  let limbValue (i: Fin 5): ZMod p := limbs i * ((2)^(51 * i.toNat))
  limbValue 0 + limbValue 1 + limbValue 2 + limbValue 3 + limbValue 4

def readLimb? (p: Pointer) (i: Fin 5) (m: MemoryState) := do
  let liveBlock ← m.live? p.id
  let limb := liveBlock.bytes.extractLsb' (p.offsetInBits + 64 * i.toNat) 64
  return limb.toNat

def readFieldElem? (p: Pointer) (m: MemoryState) := do
  let l0 ← readLimb? p 0 m
  let l1 ← readLimb? p 1 m
  let l2 ← readLimb? p 2 m
  let l3 ← readLimb? p 3 m
  let l4 ← readLimb? p 4 m
  return decodeFieldElem ![l0, l1, l2, l3, l4]

abbrev IsFieldElemPtr (m: MemoryState) (p: Pointer) : Prop :=
  Fits m p (5 * 64) ∧ p.offset.toNat + (5 * 8) ≤ 2^64

theorem readLimb?_isSome {m : MemoryState} {p : Pointer} (i : Fin 5) (h : IsFieldElemPtr m p) :
    (readLimb? p i m).isSome := by
  obtain ⟨⟨block, hblk, -⟩, -⟩ := h
  have hlive : m.live? p.id = some block := by
    simp only [MemoryState.live?, hblk]
  simp [readLimb?, hlive]

theorem readFieldElem?_isSome {m : MemoryState} {p : Pointer} (h : IsFieldElemPtr m p) :
    (readFieldElem? p m).isSome := by
  -- one opaque handle for all five limbs, each `some` by `readLimb?_isSome`
  obtain ⟨l, hl⟩ : ∃ l : Fin 5 → ℕ, ∀ i, readLimb? p i m = some (l i) :=
    ⟨fun i => (readLimb? p i m).get (readLimb?_isSome i h),
      fun i => (Option.some_get _).symm⟩
  simp [readFieldElem?, hl]

def readFieldElem (p: Pointer) (m: MemoryState) (h: IsFieldElemPtr m p) := (readFieldElem? p m).get (readFieldElem?_isSome h)

def readLimb (p: Pointer) (i : Fin 5) (m : MemoryState) (h: IsFieldElemPtr m p) := (readLimb? p i m).get (readLimb?_isSome i h)

abbrev LimbBounds {p: Pointer} (h: IsFieldElemPtr m p) := ∀ i, readLimb p i m h ≤ 0x8000000000000

/-- `LimbBounds` in the `readLimb?`-shaped form the conformance lemmas take.
`readLimb?` carries no proof argument, so this is also the form to rewrite the
pointer in. -/
theorem limbBounds_readLimb? {m : MemoryState} {q : Pointer} (h : IsFieldElemPtr m q)
    (hb : LimbBounds h) :
    ∀ (j : Fin 5) (l : ℕ), readLimb? q j m = some l → l ≤ 2 ^ 51 := by
  intro j l hl
  have hj := hb j
  simp only [readLimb, hl, Option.get_some] at hj
  exact le_trans hj (by norm_num)

/-- The converse of `limbBounds_readLimb?`, for interfaces stated in the
`readLimb?` form: the total read is `some` of itself. -/
theorem limbBounds_of_readLimb? {m : MemoryState} {q : Pointer} (h : IsFieldElemPtr m q)
    (hb : ∀ (j : Fin 5) (l : ℕ), readLimb? q j m = some l → l ≤ 2 ^ 51) :
    LimbBounds h :=
  fun j => hb j _ (Option.some_get _).symm

/-- `LimbBounds` transported along an equality of pointers. The proof argument
lives under `readLimb`, so the pointer cannot be rewritten in place; `subst`
plus proof irrelevance does it. -/
theorem limbBounds_congr {m : MemoryState} {q₁ q₂ : Pointer} (hq : q₁ = q₂)
    {h₁ : IsFieldElemPtr m q₁} {h₂ : IsFieldElemPtr m q₂} (hb : LimbBounds h₁) :
    LimbBounds h₂ := by
  subst hq; exact hb

/-- Equivalent states have the same live blocks, and a limb read looks at
nothing else. -/
theorem readLimb?_of_equiv {s s' : GlobalState} (h : s ≈ s') (p : Pointer) (i : Fin 5) :
    readLimb? p i s.mem = readLimb? p i s'.mem := by
  simp only [readLimb?, h.2 p.id]

/-- `LimbBounds` transported along a state equivalence: a limb read looks only
at the live block, and `≈` preserves that. -/
theorem limbBounds_of_equiv {s s' : GlobalState} (h : s ≈ s') {q : Pointer}
    {h₁ : IsFieldElemPtr s.mem q} {h₂ : IsFieldElemPtr s'.mem q}
    (hb : LimbBounds h₁) : LimbBounds h₂ := by
  intro i
  simp only [readLimb, ← readLimb?_of_equiv h q i]
  exact hb i

theorem readFieldElem?_of_equiv {s s' : GlobalState} (h : s ≈ s') (p : Pointer) :
    readFieldElem? p s.mem = readFieldElem? p s'.mem := by
  simp only [readFieldElem?, readLimb?_of_equiv h]

end Firedancer.Ref

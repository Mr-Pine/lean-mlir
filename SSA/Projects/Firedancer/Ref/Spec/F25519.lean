import Mathlib.Data.Fin.VecNotation
import SSA.Projects.Firedancer.Curve
import SSA.Projects.Firedancer.Ed25519
import SSA.Projects.SLLVM.Dialect

namespace Firedancer.Ref
open LeanMLIR SLLVM

def decodeFieldElem (limbs: Fin 5 → ℕ) :=
  let limbValue (i: Fin 5): ZMod p := limbs i * ((2)^(51 * i.toNat))
  limbValue 0 + limbValue 1 + limbValue 2 + limbValue 3 + limbValue 4

/-- The five limbs packed little-endian into the one word `splice` stores. -/
def packLimbs (l: Fin 5 → BitVec 64) : BitVec (5 * 64) :=
  l 4 ++ l 3 ++ l 2 ++ l 1 ++ l 0

/-- `bv_decide` needs the five limbs as plain variables, not as applications of
an opaque `l`. -/
private lemma extractLsb'_concat (a b c d e : BitVec 64) (i : Fin 5) :
    (e ++ d ++ c ++ b ++ a).extractLsb' (64 * i.toNat) 64 = ![a, b, c, d, e] i := by
  fin_cases i <;> simp <;> bv_decide

@[simp] theorem extractLsb'_packLimbs (l: Fin 5 → BitVec 64) (i : Fin 5) :
    (packLimbs l).extractLsb' (64 * i.toNat) 64 = l i := by
  rw [packLimbs, extractLsb'_concat]
  fin_cases i <;> rfl

/-- ... and the other way round: splitting a word into limbs and packing them
back is the identity. -/
theorem packLimbs_extractLsb' (x : BitVec (5 * 64)) :
    packLimbs (fun i => x.extractLsb' (64 * i.toNat) 64) = x := by
  have h : packLimbs (fun i : Fin 5 => x.extractLsb' (64 * i.toNat) 64)
      = x.extractLsb' 256 64 ++ x.extractLsb' 192 64 ++ x.extractLsb' 128 64
        ++ x.extractLsb' 64 64 ++ x.extractLsb' 0 64 := rfl
  rw [h]
  bv_decide

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

/-- The 32-byte little-endian buffer at `p`, read as one 256-bit word. -/
def readBuf? (p: Pointer) (m: MemoryState) : Option (BitVec 256) := do
  let liveBlock ← m.live? p.id
  return liveBlock.bytes.extractLsb' p.offsetInBits 256

/-- `fiat_25519_from_bytes` masks the top byte to 7 bits, so only the low 255
bits of the buffer contribute. Non-canonical encodings are accepted: the result
is reduced mod `p`, not rejected. -/
def decodeBytes (buf: BitVec 256) : ZMod p := ((buf.extractLsb' 0 255).toNat : ZMod p)

abbrev IsByteBufPtr (m: MemoryState) (p: Pointer) : Prop :=
  Fits m p (32 * 8) ∧ p.offset.toNat + 32 ≤ 2^64

theorem readBuf?_isSome {m : MemoryState} {p : Pointer} (h : IsByteBufPtr m p) :
    (readBuf? p m).isSome := by
  obtain ⟨⟨block, hblk, -⟩, -⟩ := h
  have hlive : m.live? p.id = some block := by
    simp only [MemoryState.live?, hblk]
  simp [readBuf?, hlive]

def readBuf (p: Pointer) (m: MemoryState) (h: IsByteBufPtr m p) := (readBuf? p m).get (readBuf?_isSome h)

/-- A store leaves live blocks and their sizes alone, so a field element that
fitted at `q` before still fits after a splice anywhere. -/
theorem isFieldElemPtr_splice {m : MemoryState} {p q : Pointer} {w : Nat} {x : BitVec w}
    (h : IsFieldElemPtr m q) : IsFieldElemPtr (m.splice p x) q :=
  ⟨fits_splice h.left, h.right⟩

def readFieldElem {p: Pointer} {m: MemoryState} (h: IsFieldElemPtr m p) := (readFieldElem? p m).get (readFieldElem?_isSome h)

def readLimb (p: Pointer) (i : Fin 5) (m : MemoryState) (h: IsFieldElemPtr m p) := (readLimb? p i m).get (readLimb?_isSome i h)

/-- Every limb at `p` is at most `bound`, which defaults to the tight bound
`2^51` a carried field element satisfies. `fiat_25519_add`/`sub` leave a loose
element, so they pass the larger bound explicitly. -/
abbrev LimbBounds (h: IsFieldElemPtr m q) (bound : ℕ := 0x8000000000000) :=
  ∀ i, readLimb q i m h ≤ bound

abbrev LimbBounds.Loose (h : IsFieldElemPtr m q) := LimbBounds h 0x18000000000000

lemma LimbBounds.loose (lb : LimbBounds h) : LimbBounds.Loose h :=  fun i => le_trans (lb i) (by norm_num)


/-- `LimbBounds` in the `readLimb?`-shaped form the conformance lemmas take.
`readLimb?` carries no proof argument, so this is also the form to rewrite the
pointer in. -/
theorem limbBounds_readLimb? {m : MemoryState} {q : Pointer} {bound : ℕ}
    (h : IsFieldElemPtr m q) (hb : LimbBounds h bound) :
    ∀ (j : Fin 5) (l : ℕ), readLimb? q j m = some l → l ≤ bound := by
  intro j l hl
  have hj := hb j
  simp only [readLimb, hl, Option.get_some] at hj
  exact hj

/-- The converse of `limbBounds_readLimb?`, for interfaces stated in the
`readLimb?` form: the total read is `some` of itself. -/
theorem limbBounds_of_readLimb? {m : MemoryState} {q : Pointer} {bound : ℕ}
    (h : IsFieldElemPtr m q)
    (hb : ∀ (j : Fin 5) (l : ℕ), readLimb? q j m = some l → l ≤ bound) :
    LimbBounds h bound :=
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

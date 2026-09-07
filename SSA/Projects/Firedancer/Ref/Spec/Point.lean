import Mathlib.Data.Fin.VecNotation
import SSA.Projects.Firedancer.Curve
import SSA.Projects.Firedancer.Ed25519
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref
open LeanMLIR SLLVM
open Ed25519

def decodePoint (coords: Fin 4 → ZMod p) : Point :=
  { X := coords 0, Y := coords 1, Z := coords 3, T := coords 2 }

def readCoordinate? (p: Pointer) (i: Fin 4) := readFieldElem? (p.withOffset (i * (5 * 8)))

def readPoint? (p: Pointer) (m: MemoryState) := do
  let X ← readCoordinate? p 0 m
  let Y ← readCoordinate? p 1 m
  let T ← readCoordinate? p 2 m
  let Z ← readCoordinate? p 3 m
  return decodePoint ![X, Y, T, Z]

abbrev IsPointPtr (m: MemoryState) (p: Pointer) : Prop :=
  Fits m p (4 * 5 * 64) ∧ p.offset.toNat + (4 * 5 * 8) ≤ 2^64

theorem isCoordPtr {p : Pointer} (h : IsPointPtr m p) (i : Fin 4) :
  IsFieldElemPtr m (p.withOffset (i * (5 * 8))) := by
  obtain ⟨⟨blk, hblk, hlen⟩, hnw⟩ := h
  refine ⟨⟨blk, hblk, ?_⟩, ?_⟩ <;>
    fin_cases i <;>
    simp [Pointer.withOffset, Pointer.offsetInBits, LiveBlock.lengthInBits,
      BitVec.toNat_add] at hlen ⊢ <;>
    omega

/-- A store leaves live blocks and their sizes alone, so a point that fitted
at `q` before still fits after a splice anywhere -- the point counterpart of
`isFieldElemPtr_splice`. -/
theorem isPointPtr_splice {m : MemoryState} {q₁ q₂ : Pointer} {w : Nat} {x : BitVec w}
    (h : IsPointPtr m q₂) : IsPointPtr (m.splice q₁ x) q₂ :=
  ⟨fits_splice h.left, h.right⟩

abbrev AllLimbBounds {p : Pointer} {m: MemoryState} (h : IsPointPtr m p) := ∀ (i : Fin 4),
  let fieldElemPtr := p.withOffset (i * (5 * 8))
  have hf : IsFieldElemPtr m fieldElemPtr := by exact isCoordPtr h i
  LimbBounds hf

theorem readPoint?_isSome {m : MemoryState} {p : Pointer} (h : IsPointPtr m p) :
    (readPoint? p m).isSome := by
  obtain ⟨⟨block, hblk, -⟩, -⟩ := h
  have hlive : m.live? p.id = some block := by
    simp only [MemoryState.live?, hblk]
  simp [readPoint?, readCoordinate?, readFieldElem?, readLimb?, Pointer.withOffset, hlive]

def readPoint {p: Pointer} {m: MemoryState} (h: IsPointPtr m p) : Point := (readPoint? p m).get (readPoint?_isSome h)

end Firedancer.Ref

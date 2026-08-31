import SSA.Projects.Firedancer.Ref.Spec.Point
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

/-!
# Reading a point

Lemmas about `readPoint` and the coordinate pointers a region geps. None of
these is needed to state a spec; they are what the conformance proofs use to
line a `readPoint` up with the four field-element reads underneath it.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM
open Ed25519

/-- The tight bound, as the `readLimb?`-shaped hypothesis the per-field-element
lemmas take: every limb of coordinate `i` is at most `2^51`. -/
theorem coordLimbBounds {m : MemoryState} {p : Pointer}
    (h : IsPointPtr m p) (hb : AllLimbBounds h) (i : Fin 4) :
    have coordPtr := isCoordPtr p h i
    LimbBounds coordPtr := hb i

/-- Coordinate 0 sits at the base pointer: where a `getelementptr` by field 0
would go, a region passes the argument itself. -/
theorem coordPtr_zero (p : Pointer) : p.withOffset ((0 : Fin 4) * (5 * 8)) = p := by
  simp [Pointer.withOffset]

/-- The coordinate pointers, at the byte offsets a region's `getelementptr`s
compute. -/
theorem coordPtr_one (p : Pointer) : p.withOffset ((1 : Fin 4) * (5 * 8)) = p.withOffset 40 := rfl
theorem coordPtr_three (p : Pointer) : p.withOffset ((3 : Fin 4) * (5 * 8)) = p.withOffset 120 := rfl

/-- A point read off its four coordinate reads. -/
theorem readPoint_eq {m : MemoryState} {ptr : Pointer} (h : IsPointPtr m ptr) {c : Fin 4 → ZMod p}
    (hc : ∀ i, readCoordinate? ptr i m = some (c i)) :
    readPoint h = decodePoint c := by
  have : readPoint? ptr m = some (decodePoint c) := by
    simp only [readPoint?, hc, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      decodePoint, Matrix.cons_val_zero, Matrix.cons_val_one]
    rfl
  simp only [readPoint, this, Option.get_some]

theorem readCoordinate?_zero (ptr : Pointer) (m : MemoryState) :
    readCoordinate? ptr 0 m = readFieldElem? ptr m := by
  simp only [readCoordinate?, coordPtr_zero]
theorem readCoordinate?_one (ptr : Pointer) (m : MemoryState) :
    readCoordinate? ptr 1 m = readFieldElem? (ptr.withOffset 40) m := rfl
theorem readCoordinate?_three (ptr : Pointer) (m : MemoryState) :
    readCoordinate? ptr 3 m = readFieldElem? (ptr.withOffset 120) m := rfl

/-- `X`, `Y` and `Z` of a `readPoint`, as reads at the coordinate pointers. -/
theorem readPoint_coords {m : MemoryState} {ptr : Pointer} (h : IsPointPtr m ptr) :
    readFieldElem? ptr m = some (readPoint h).X
      ∧ readFieldElem? (ptr.withOffset 40) m = some (readPoint h).Y
      ∧ readFieldElem? (ptr.withOffset 120) m = some (readPoint h).Z := by
  obtain ⟨c, hc⟩ : ∃ c : Fin 4 → ZMod p, ∀ i, readCoordinate? ptr i m = some (c i) :=
    ⟨fun i => (readCoordinate? ptr i m).get (readFieldElem?_isSome (isCoordPtr ptr h i)),
      fun i => (Option.some_get _).symm⟩
  rw [readPoint_eq h hc]
  exact ⟨(readCoordinate?_zero ptr m).symm.trans (hc 0),
    (readCoordinate?_one ptr m).symm.trans (hc 1),
    (readCoordinate?_three ptr m).symm.trans (hc 3)⟩

theorem readCoordinate?_of_equiv {s s' : GlobalState} (h : s ≈ s') (p : Pointer) (i : Fin 4) :
    readCoordinate? p i s.mem = readCoordinate? p i s'.mem := by
  simp only [readCoordinate?, readFieldElem?_of_equiv h]

theorem readPoint?_of_equiv {s s' : GlobalState} (h : s ≈ s') (p : Pointer) :
    readPoint? p s.mem = readPoint? p s'.mem := by
  simp only [readPoint?, readCoordinate?_of_equiv h]


end Firedancer.Ref

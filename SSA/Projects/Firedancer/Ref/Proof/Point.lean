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
theorem coordLimbBounds {m : MemoryState} {p : Pointer} (h : IsPointPtr m p) (hb : AllLimbBounds h)
    (i : Fin 4) :
    have coordPtr := isCoordPtr h i
    LimbBounds coordPtr :=
  hb i

/-- Coordinate 0 sits at the base pointer: where a `getelementptr` by field 0
would go, a region passes the argument itself. -/
theorem coordPtr_zero (p : Pointer) : p.withOffset ((0 : Fin 4) * (5 * 8)) = p := by
  simp [Pointer.withOffset]

/-- The coordinate pointers, at the byte offsets a region's `getelementptr`s
compute. -/
theorem coordPtr_one (p : Pointer) : p.withOffset ((1 : Fin 4) * (5 * 8)) = p.withOffset 40 :=
  rfl

theorem coordPtr_two (p : Pointer) : p.withOffset ((2 : Fin 4) * (5 * 8)) = p.withOffset 80 :=
  rfl

theorem coordPtr_three (p : Pointer) : p.withOffset ((3 : Fin 4) * (5 * 8)) = p.withOffset 120 :=
  rfl

/-- `readLimb` is `readLimb?` with the `isSome` proof supplied, and its value
does not depend on that proof -- so an equation between the partial reads is
one between the total ones. -/
theorem readLimb_eq_of_readLimb? {m m' : MemoryState} {q q' : Pointer} {i : Fin 5}
    {h : IsFieldElemPtr m q} {h' : IsFieldElemPtr m' q'}
    (he : readLimb? q i m = readLimb? q' i m') : readLimb i h = readLimb i h' := by
  simp only [readLimb, he]

/-- Limb for limb is field element for field element. -/
theorem readFieldElem_eq_of_readLimb {m m' : MemoryState} {q q' : Pointer} {h : IsFieldElemPtr m q}
    {h' : IsFieldElemPtr m' q'} (hl : ∀ i, readLimb i h = readLimb i h') :
    readFieldElem h = readFieldElem h' := by
  rw [readFieldElem_eq_decode, readFieldElem_eq_decode]
  simp only [hl]

/-- A point pointer looks only at the block it addresses -- the point
counterpart of `isFieldElemPtr_of_live?_eq`. -/
theorem isPointPtr_of_live?_eq {m m' : MemoryState} {r : Pointer} (h : m'.live? r.id = m.live? r.id)
    (hr : IsPointPtr m r) : IsPointPtr m' r :=
  ⟨fits_of_live?_eq h hr.left, hr.right⟩

/-- The point counterpart of `isByteBufPtr_of_equiv`, in the same shape and
for the same reason. -/
theorem isPointPtr_of_equiv {w s : GlobalState} {m : MemoryState} {r : Pointer}
    (he : w ≈ ({ s with mem := m } : GlobalState)) (h : IsPointPtr m r) : IsPointPtr w.mem r :=
  isPointPtr_of_live?_eq (live?_of_equiv_mem he r.id) h

/-- A point read looks only at the block it addresses, so two memories that
agree on that block read the same point -- what bridges the caller's memory
and the callee's, whose frames differ everywhere else. -/
theorem readPoint_of_live?_eq {m m' : MemoryState} {r : Pointer}
    (hlive : m'.live? r.id = m.live? r.id) (h : IsPointPtr m r) (h' : IsPointPtr m' r) :
    readPoint h' = readPoint h := by
  have e : ∀ i : Fin 4, readCoordinate? r i m' = readCoordinate? r i m := fun i =>
    readFieldElem?_of_live?_eq (p := r.withOffset (i * (5 * 8))) hlive
  simp only [readPoint, readPoint?, e]

/-- A point read off its four coordinate reads. -/
theorem readPoint_eq {m : MemoryState} {ptr : Pointer} (h : IsPointPtr m ptr) {c : Fin 4 → ZMod p}
    (hc : ∀ i, readCoordinate? ptr i m = some (c i)) : readPoint h = decodePoint c := by
  have : readPoint? ptr m = some (decodePoint c) := by
    simp only [readPoint?, hc, Option.bind_eq_bind, Option.bind_some, Option.pure_def, decodePoint,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rfl
  simp only [readPoint, this, Option.get_some]

theorem readCoordinate?_zero (ptr : Pointer) (m : MemoryState) :
    readCoordinate? ptr 0 m = readFieldElem? ptr m := by simp only [readCoordinate?, coordPtr_zero]

theorem readCoordinate?_one (ptr : Pointer) (m : MemoryState) :
    readCoordinate? ptr 1 m = readFieldElem? (ptr.withOffset 40) m :=
  rfl

theorem readCoordinate?_three (ptr : Pointer) (m : MemoryState) :
    readCoordinate? ptr 3 m = readFieldElem? (ptr.withOffset 120) m :=
  rfl

/-- `X`, `Y` and `Z` of a `readPoint`, as reads at the coordinate pointers. -/
theorem readPoint_coords {m : MemoryState} {ptr : Pointer} (h : IsPointPtr m ptr) :
    readFieldElem? ptr m = some (readPoint h).X ∧
      readFieldElem? (ptr.withOffset 40) m = some (readPoint h).Y ∧
      readFieldElem? (ptr.withOffset 120) m = some (readPoint h).Z := by
  obtain ⟨c, hc⟩ : ∃ c : Fin 4 → ZMod p, ∀ i, readCoordinate? ptr i m = some (c i) :=
    ⟨fun i => (readCoordinate? ptr i m).get (readFieldElem?_isSome (isCoordPtr h i)), fun i =>
      (Option.some_get _).symm⟩
  rw [readPoint_eq h hc]
  exact
    ⟨(readCoordinate?_zero ptr m).symm.trans (hc 0), (readCoordinate?_one ptr m).symm.trans (hc 1),
      (readCoordinate?_three ptr m).symm.trans (hc 3)⟩

theorem readCoordinate?_of_equiv {s s' : GlobalState} (h : s ≈ s') (p : Pointer) (i : Fin 4) :
    readCoordinate? p i s.mem = readCoordinate? p i s'.mem := by
  simp only [readCoordinate?, readFieldElem?_of_equiv h]

theorem readPoint?_of_equiv {s s' : GlobalState} (h : s ≈ s') (p : Pointer) :
    readPoint? p s.mem = readPoint? p s'.mem := by
  simp only [readPoint?, readCoordinate?_of_equiv h]

/-- The point at `ptr`, read off its four coordinate *field elements* rather
than its twenty limbs -- the form a caller of `fd_ed25519_point_from` has them
in. The four witnesses are implicit and *uncast*: writing them as
`coordPtr_one ptr ▸ isCoordPtr h 1` in the statement makes every
application recompute a `▸` motive over the caller's memory term, which for a
four-fold splice is minutes of `whnf`. Note the field order: `decodePoint` puts coordinate 2 in `T` and
coordinate 3 in `Z`, matching the struct's `X, Y, T, Z`. -/
theorem readPoint_eq_of {m : MemoryState} {ptr : Pointer} (h : IsPointPtr m ptr) {X Y T Z : ZMod p}
    {h0 : IsFieldElemPtr m ptr} {h1 : IsFieldElemPtr m (ptr.withOffset 40)}
    {h2 : IsFieldElemPtr m (ptr.withOffset 80)} {h3 : IsFieldElemPtr m (ptr.withOffset 120)}
    (hX : readFieldElem h0 = X) (hY : readFieldElem h1 = Y) (hT : readFieldElem h2 = T)
    (hZ : readFieldElem h3 = Z) : readPoint h = { X := X, Y := Y, Z := Z, T := T } := by
  refine (readPoint_eq h (c := ![X, Y, T, Z]) ?_).trans rfl
  intro i
  have get :
    ∀ {q : Pointer} {hq : IsFieldElemPtr m q} {v : ZMod p},
      readFieldElem hq = v → readFieldElem? q m = some v := by
    rintro q hq v rfl; exact (Option.some_get _).symm
  fin_cases i
  · simpa [readCoordinate?, Pointer.withOffset] using get hX
  · simpa [readCoordinate?, coordPtr_one] using get hY
  · simpa [readCoordinate?, coordPtr_two] using get hT
  · simpa [readCoordinate?, coordPtr_three] using get hZ

end Firedancer.Ref

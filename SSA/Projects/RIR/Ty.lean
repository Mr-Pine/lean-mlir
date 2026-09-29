module

public import SSA.Projects.RIR.Poison
public import SSA.Projects.RIR.Memory.Pointer
public import Lean.ToExpr

namespace LeanMLIR.RIR

public inductive Ty
  | bv (w : Nat)
  | ptr
  | vec (l w : Nat)

namespace Ty

@[expose] public section

deriving instance DecidableEq, Lean.ToExpr, Repr for Ty

@[reducible]
def denote_raw
  | bv w => BitVec w
  | ptr => Pointer
  | vec l w => Vector (BitVec w) l

notation "⟦" t "⟧ᵣ" => LeanMLIR.RIR.Ty.denote_raw t

@[reducible]
def denote
  | bv w => PoisonOr (BitVec w)
  | ptr => PoisonOr (Pointer)
  | vec l w => Vector (PoisonOr (BitVec w)) l

/-- `⟦t⟧` is the `Type` of values of (MLIR) type `t` --/
notation "⟦" t "⟧" => LeanMLIR.RIR.Ty.denote t

instance instDecidableEqDenoteRaw : {t : Ty} → DecidableEq ⟦t⟧
  | .bv _ => inferInstanceAs (DecidableEq (PoisonOr (BitVec _)))
  | .ptr => inferInstanceAs (DecidableEq (PoisonOr Pointer))
  | .vec _ _ => inferInstanceAs (DecidableEq (Vector (PoisonOr (BitVec _)) _))

instance instDecidableEqDenote : {t : Ty} → DecidableEq ⟦t⟧ᵣ
  | .bv _ => inferInstanceAs (DecidableEq (BitVec _))
  | .ptr => inferInstanceAs (DecidableEq Pointer)
  | .vec _ _ => inferInstanceAs (DecidableEq (Vector (BitVec _) _))

def unwrap (v : ⟦t⟧) : PoisonOr ⟦t⟧ᵣ :=
  match t with
  | bv _ => v
  | ptr => v
  | vec _ _ => Vector.mapM id v

@[simp]
theorem unwrap_bv {v : ⟦bv w⟧} : unwrap v = v :=
  rfl

end

public section

@[expose]
def width : Ty → Nat
  | bv w => w
  | ptr => 64
  | vec l w => w * l

def poisoned : (t : Ty) → ⟦t⟧
  | .bv _ | .ptr => PoisonOr.poison
  | .vec l _ => Vector.replicate l PoisonOr.poison

@[simp]
theorem width_bv : (bv w).width = w :=
  rfl

@[simp]
theorem width_vec : (vec l w).width = w * l :=
  rfl

@[simp]
theorem poisoned_bv : poisoned (bv w) = (.poison : PoisonOr (BitVec w)) := by rfl

@[simp]
theorem poisoned_ptr : poisoned ptr = (.poison : PoisonOr Pointer) := by rfl

end

public section FlattenUnflatten

section BitVecs

/-- Pack a Vector of BitVectors into one. -/
def _root_.BitVec.packLanes {we : Nat} : {n : Nat} → Vector (BitVec we) n → BitVec (we * n)
  | 0, _ => 0#(we * 0)
  | _ + 1, v => BitVec.packLanes v.tail ++ v[0]

/-- Lane `i` of a packed bitvector is the `i`-th input lane. -/
theorem _root_.BitVec.extractLsb'_packLanes {we : Nat} :
    ∀ {n : Nat} (v : Vector (BitVec we) n) (i : Nat) (h : i < n),
      (BitVec.packLanes v).extractLsb' (i * we) we = v[i]
  | 0, _, _, h => absurd h (by omega)
  | _ + 1, v, 0, _ => by
    simpa [BitVec.packLanes] using
      (BitVec.extractLsb'_append_eq_right (a := BitVec.packLanes v.tail) (b := v[0]))
  | n + 1, v, i + 1, h => by
    have hi : i < n := by omega
    have key :
      (BitVec.packLanes v).extractLsb' ((i + 1) * we) we =
        (BitVec.packLanes v.tail).extractLsb' (i * we) we := by
      have hunfold :
        (BitVec.packLanes v).extractLsb' ((i + 1) * we) we =
          (BitVec.packLanes v.tail ++ v[0]).extractLsb' ((i + 1) * we) we :=
        rfl
      rw [hunfold, show (i + 1) * we = i * we + we from Nat.succ_mul i we,
        BitVec.extractLsb'_append_eq_of_le (Nat.le_add_left we (i * we))]
      congr 1
      omega
    rw [key, BitVec.extractLsb'_packLanes v.tail i hi]
    simp [Nat.add_comm]

end BitVecs

def flatten : (t : Ty) → ⟦t⟧ → PoisonOr (BitVec t.width)
  | bv _, x => x
  | ptr, _ => .poison
  | vec l _, v =>
    if ∀ i : Fin l, v[i] ≠ .poison then
      .value (BitVec.packLanes (Vector.ofFn (n := l) fun i => v[i].getValue))
    else .poison

def unflatten : (t : Ty) → BitVec t.width → ⟦t⟧
  | bv _, x => .value x
  | ptr, _ => .poison
  | vec _ w, x => Vector.ofFn (fun i => .value (x.extractLsb' (i.val * w) w))

@[simp]
theorem flatten_bv (x : ⟦bv w⟧) : flatten (bv w) x = x := by rfl

@[simp]
theorem unflatten_bv (b : BitVec w) : unflatten (bv w) b = .value b := by rfl

@[simp]
theorem flatten_ptr (x : ⟦ptr⟧) : flatten ptr x = .poison := by rfl

theorem unflatten_flatten {t : Ty} {v : ⟦t⟧} {b : BitVec t.width} (h : flatten t v = .value b) :
    unflatten t b = v := by
  cases t with
  | bv w =>
    cases v; simp_all [flatten, unflatten]
  | ptr => exact absurd h (PoisonOr.poison_ne_value b)
  | vec l w =>
    simp_all [flatten, unflatten, denote]
    have : ∀ (i : Fin l), ¬v[↑i] = PoisonOr.poison := by
      apply Decidable.by_contra; intro h'
      rw [ite_eq_right] at h
      · exact (PoisonOr.value_ne_poison b).symm h
      · simp at *
        assumption
    dsimp at *
    dsimp [width_vec] at b
    rw [ite_eq_left] at h
    · rw [PoisonOr.value_inj] at h
      rw [← h]
      ext i hi
      simp
      rw [BitVec.extractLsb'_packLanes (h := hi)]
      replace this := this ⟨i, hi⟩
      simp at this
      obtain ⟨x, hx⟩ : ∃ x, v[i] = .value x := by
        exists (v[i].getValue)
        rotate_left
        cases h : v[i]
        · have := this h
          simp at *
        case value x => rfl
      simp [hx]
    exact this

end FlattenUnflatten

end LeanMLIR.RIR.Ty

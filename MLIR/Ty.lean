module

public import MLIR.SimpSets
public import MLIR.Poison
public import MLIR.Memory.Pointer
public import Lean.ToExpr

namespace MLIR

public inductive Ty
  | bv (w : Nat)
  | ptr
  | vec (l w : Nat)
  | array (n : Nat) (t : Ty)
  | struct (fields : List Ty)

namespace Ty

@[expose] public section

mutual
def Ty.decEq : (a b : Ty) → Decidable (a = b)
  | .bv w, .bv w' => if h : w = w' then isTrue (h ▸ rfl) else isFalse (fun e => h (Ty.bv.inj e))
  | .ptr, .ptr => isTrue rfl
  | .vec l w, .vec l' w' =>
    if h : l = l' ∧ w = w' then isTrue (h.left ▸ (h.right ▸ rfl))
    else isFalse (fun e => h (Ty.vec.inj e))
  | .array n t, .array n' t' =>
    haveI := decEq t t'
    if h : n = n' ∧ t = t' then isTrue (h.left ▸ (h.right ▸ rfl))
    else isFalse (fun e => h (Ty.array.inj e))
  | .struct fields, .struct fields' =>
    haveI := decEqList fields fields'
    if h : fields = fields' then isTrue (h ▸ rfl) else isFalse (fun e => h (Ty.struct.inj e))
  -- There seems to be no nicer way :(
  | .bv _, .ptr | .bv _, .vec .. | .bv _, .array .. | .bv _, .struct _ | .ptr, .bv _ | .ptr,
    .vec .. | .ptr, .array .. | .ptr, .struct _ | .vec .., .bv _ | .vec .., .ptr | .vec ..,
    .array .. | .vec .., .struct _ | .array .., .bv _ | .array .., .ptr | .array .., .vec .. |
    .array .., .struct _ | .struct _, .bv _ | .struct _, .ptr | .struct _, .vec .. | .struct _,
    .array .. =>
    isFalse
      (by
        intro e; cases e)
def Ty.decEqList : (a b : List Ty) → Decidable (a = b)
  | [], [] => isTrue rfl
  | t :: ts, t' :: ts' =>
    haveI := decEq t t'
    haveI := decEqList ts ts'
    if h : t = t' ∧ ts = ts' then isTrue (List.cons_eq_cons.mpr h)
    else isFalse (fun e => h (List.cons_eq_cons.mp e))
  | [], t :: ts | t :: ts, [] => isFalse (by simp)
end

deriving instance Lean.ToExpr, Repr for Ty

instance : DecidableEq Ty :=
  Ty.decEq

mutual
@[reducible]
def denoteRaw : Ty → Type
  | bv w => BitVec w
  | ptr => Pointer
  | vec l w => Vector (BitVec w) l
  | array n τ => Vector (denoteRaw τ) n
  | struct fields => denoteFieldsRaw fields
@[reducible]
def denoteFieldsRaw : List Ty → Type
  | [] => Unit
  | [t] => denoteRaw t
  | t :: ts => denoteRaw t × denoteFieldsRaw ts
end

notation "⟦" t "⟧ᵣ" => denoteRaw t

mutual
@[reducible]
def denote
  | bv w => PoisonOr (BitVec w)
  | ptr => PoisonOr (Pointer)
  | vec l w => Vector (PoisonOr (BitVec w)) l
  | array n τ => Vector (denote τ) n
  | struct fields => denoteFields fields
@[reducible]
def denoteFields : List Ty → Type
  | [] => Unit
  | [t] => denote t
  | t :: ts => denote t × denoteFields ts
end

/-- `⟦t⟧` is the `Type` of values of (MLIR) type `t` --/
notation "⟦" t "⟧" => MLIR.Ty.denote t

mutual
def decEqDenoteRaw : (t : Ty) → DecidableEq ⟦t⟧ᵣ
  | .bv _ => inferInstanceAs (DecidableEq (BitVec _))
  | .ptr => inferInstanceAs (DecidableEq Pointer)
  | .vec _ _ => inferInstanceAs (DecidableEq (Vector (BitVec _) _))
  | .array _ t =>
    haveI := decEqDenoteRaw t
    inferInstanceAs (DecidableEq (Vector ⟦t⟧ᵣ _))
  | .struct fs => decEqDenoteFieldsRaw fs
def decEqDenoteFieldsRaw : (ts : List Ty) → DecidableEq (denoteFieldsRaw ts)
  | [] => inferInstanceAs (DecidableEq Unit)
  | [t] => decEqDenoteRaw t
  | t :: t' :: ts =>
    haveI := decEqDenoteRaw t
    haveI := decEqDenoteFieldsRaw (t' :: ts)
    inferInstanceAs (DecidableEq (⟦t⟧ᵣ × denoteFieldsRaw (t' :: ts)))
end

instance {t : Ty} : DecidableEq ⟦t⟧ᵣ :=
  decEqDenoteRaw t

mutual
def decEqDenote : (t : Ty) → DecidableEq ⟦t⟧
  | .bv _ => inferInstanceAs (DecidableEq (PoisonOr (BitVec _)))
  | .ptr => inferInstanceAs (DecidableEq (PoisonOr Pointer))
  | .vec _ _ => inferInstanceAs (DecidableEq (Vector (PoisonOr (BitVec _)) _))
  | .array _ t =>
    haveI := decEqDenote t
    inferInstanceAs (DecidableEq (Vector ⟦t⟧ _))
  | .struct fs => decEqDenoteFields fs
def decEqDenoteFields : (ts : List Ty) → DecidableEq (denoteFields ts)
  | [] => inferInstanceAs (DecidableEq Unit)
  | [t] => decEqDenote t
  | t :: t' :: ts =>
    haveI := decEqDenote t
    haveI := decEqDenoteFields (t' :: ts)
    inferInstanceAs (DecidableEq (⟦t⟧ × denoteFields (t' :: ts)))
end

instance {t : Ty} : DecidableEq ⟦t⟧ :=
  decEqDenote t

mutual
def wrap (v : ⟦t⟧ᵣ) : ⟦t⟧ :=
  match t with
  | bv _ => .value v
  | ptr => .value v
  | vec _ _ => Vector.map .value v
  | array _ _ => Vector.map wrap v
  | struct _ => wrapFields v
def wrapFields : {fs : List Ty} → denoteFieldsRaw fs → denoteFields fs
  | [], _ => ()
  | [_], v => wrap v
  | _ :: _ :: _, (v, vs) => (wrap v, wrapFields vs)
end

mutual
def unwrap (v : ⟦t⟧) : PoisonOr ⟦t⟧ᵣ :=
  match t with
  | bv _ => v
  | ptr => v
  | vec _ _ => Vector.mapM id v
  | array _ _ => Vector.mapM unwrap v
  | struct _ => unwrapFields v
def unwrapFields : {fs : List Ty} → denoteFields fs → PoisonOr (denoteFieldsRaw fs)
  | [], _ => .value ()
  | [_], v => unwrap v
  | _ :: _ :: _, (v, vs) => do
    return (← unwrap v, ← unwrapFields vs)
end

@[simp]
theorem unwrap_bv {v : ⟦bv w⟧} : unwrap v = v :=
  rfl

@[simp, mlir_operation]
theorem wrap_bv {v : ⟦bv w⟧ᵣ} : wrap v = .value v :=
  rfl

theorem wrap_vec (vs : ⟦vec l w⟧ᵣ) : wrap vs = vs.map .value := by simp [wrap]

@[simp]
theorem unwrap_wrap {v : ⟦bv w⟧ᵣ} : unwrap (wrap v) = .value v :=
  rfl

end

public section

mutual
@[expose]
def width : Ty → Nat
  | bv w => w
  | ptr => 64
  | vec l w => w * l
  | array n t => t.width * n
  | struct fields => fieldsWidth fields
@[expose]
def fieldsWidth : List Ty → Nat
  | [] => 0
  | [t] => t.width
  | t :: ts => fieldsWidth ts + t.width
end

mutual
def poisoned : (t : Ty) → ⟦t⟧
  | .bv _ | .ptr => PoisonOr.poison
  | .vec l _ => Vector.replicate l PoisonOr.poison
  | .array n t => Vector.replicate n (t.poisoned)
  | .struct fields => poisonedFields fields
def poisonedFields : (ts : List Ty) → denoteFields ts
  | [] => ()
  | [t] => t.poisoned
  | t :: t' :: ts => (t.poisoned, poisonedFields (t' :: ts))
end

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

/-- A poisoned vector is poison in every lane: an `insertelement` chain's start. -/
@[simp, mlir_operation]
theorem poisoned_vec : poisoned (vec l w) = Vector.replicate l (.poison : PoisonOr (BitVec w)) := by
  rfl

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

def allValues [Inhabited α] (v : Vector (PoisonOr α) n) : PoisonOr (Vector α n) :=
  if ∀ i : Fin n, v[i].isPoison = false then .value (Vector.ofFn fun i => v[i].getValue)
  else .poison

mutual
def flatten : (t : Ty) → ⟦t⟧ → PoisonOr (BitVec t.width)
  | bv _, x => x
  | ptr, _ => .poison
  | vec _ _, v => do
    return BitVec.packLanes (← allValues v)
  | array _ t, v => do
    return BitVec.packLanes (← allValues (v.map (flatten t)))
  | struct fields, v => flattenFields fields v
def flattenFields : (ts : List Ty) → denoteFields ts → PoisonOr (BitVec (fieldsWidth ts))
  | [], _ => .value 0#0
  | [t], v => flatten t v
  | t :: t' :: ts, (a, b) => do
    return (← flattenFields (t' :: ts) b) ++ (← flatten t a)
end

def extractVecElem (l w : Nat) (i : Fin l) (x : BitVec (w * l)) :=
  x.extractLsb' (i.val * w) w

theorem extractVecElem_eq (x : BitVec (w * l)) :
    extractVecElem l w i x = x.extractLsb' (i.val * w) w := by
  unfold extractVecElem; rfl

@[mlir_operation]
theorem extractVecElem_packLanes {xs : Vector (BitVec _) l} :
    extractVecElem l w i (BitVec.packLanes xs) = xs[i] := by
  simp [extractVecElem, BitVec.extractLsb'_packLanes]

-- a vector rebuilt from its lanes: a load of a stored vector
attribute [mlir_operation] Vector.ofFn_getElem

-- a constant vector's lanes, and the identity adds they leave (`madd52`'s zero accumulator)
attribute [mlir_operation] Vector.getElem_replicate BitVec.zero_add BitVec.add_zero
  BitVec.toNat_ofNat

mutual
def unflatten : (t : Ty) → BitVec t.width → ⟦t⟧
  | bv _, x => .value x
  | ptr, _ => .poison
  | vec _ w, x => Vector.ofFn (fun i => .value (extractVecElem _ w i x))
  | array n t, x => Vector.ofFn (fun i => unflatten t (extractVecElem n (t.width) i x))
  | struct fields, x => unflattenFields fields x
def unflattenFields : (ts : List Ty) → BitVec (fieldsWidth ts) → denoteFields ts
  | [], _ => ()
  | [t], x => unflatten t x
  | t :: t' :: ts, x =>
    let v := x.extractLsb' 0 (t.width)
    let vs := x.extractLsb' (t.width) (fieldsWidth (t' :: ts))
    (unflatten t v, unflattenFields (t' :: ts) vs)
end

@[simp]
theorem flatten_bv (x : ⟦bv w⟧) : flatten (bv w) x = x := by rfl

@[simp]
theorem unflatten_bv (b : BitVec w) : unflatten (bv w) b = .value b := by rfl

@[simp]
theorem unflatten_vec (b : BitVec (w * l)) :
    unflatten (vec l w) b = wrap (Vector.ofFn (fun i => (extractVecElem _ w i b))) := by
  ext
  simp [unflatten, wrap_vec]

@[simp]
theorem flatten_wrap_vec (v : ⟦vec l w⟧ᵣ) :
    flatten (vec l w) (wrap v) = .value (BitVec.packLanes v) := by
  simp [flatten, wrap_vec, allValues]

@[simp]
theorem flatten_ptr (x : ⟦ptr⟧) : flatten ptr x = .poison := by rfl

theorem allValues_eq_value [Inhabited α] (v : Vector (PoisonOr α) n) :
    allValues v = .value w ↔ v = w.map .value := by
  simp [allValues]
  split
  case isTrue h =>
    simp
    constructor
    · intro h'
      rw [← h']
      ext i hi
      simp
      simp [PoisonOr.isPoisonFalse_eq_existsValue] at h
      obtain ⟨w, hw⟩ := h ⟨i, hi⟩
      simp [hw]
    · intro h'
      simp [h']
  case isFalse h =>
    simp at h
    obtain ⟨i, hi⟩ := h
    have : v[i.val] = .poison := PoisonOr.isPoisonTrue_eq_eqPoison.mp hi
    simp [PoisonOr.poison_ne_value, Vector.ext_iff]
    refine ⟨i, i.isLt, ?_⟩
    simp [this, PoisonOr.poison_ne_value]

mutual
theorem unflatten_flatten {t : Ty} {v : ⟦t⟧} {b : BitVec t.width} (h : flatten t v = .value b) :
    unflatten t b = v := by
  cases t with
  | bv w =>
    cases v; simp_all [flatten, unflatten]
  | ptr => exact absurd h (PoisonOr.poison_ne_value b)
  | vec l w =>
    simp_all [flatten, unflatten, denote]
    cases h' : allValues v with
    | poison =>
      simp [h'] at h
      have := PoisonOr.poison_ne_value b h
      exfalso
      exact this
    | value w =>
      simp [h'] at h
      obtain rfl := PoisonOr.value_inj.mp h
      simp [extractVecElem_packLanes]
      ext i hi
      simp [(allValues_eq_value v).mp h']
  | array n t =>
    simp only [flatten] at h
    cases h' : allValues (v.map (t.flatten)) with
    | poison =>
      simp [h'] at h
      have := PoisonOr.poison_ne_value b h
      exfalso
      exact this
    | value w =>
      simp [h'] at h
      obtain rfl := PoisonOr.value_inj.mp h
      have := (allValues_eq_value _).mp h'
      ext i hi
      simp [unflatten, extractVecElem_packLanes]
      exact unflatten_flatten (by simpa using congrArg (·[i]) this)
  | struct fields =>
    simp [flatten, unflatten] at *
    exact unflattenFields_flattenFields h
theorem unflattenFields_flattenFields (h : flattenFields ts v = .value b) :
    unflattenFields ts b = v := by
  unfold unflattenFields
  split
  · simp
  case h_2 ts flat_ts t flat_t =>
    simp [flattenFields] at h
    exact unflatten_flatten h
  case h_3 a b t t' ts flat =>
    simp
    rw [flattenFields] at h
    obtain ⟨bs, hbs, h⟩ := PoisonOr.bind_eq_value.mp h
    obtain ⟨b, hb, h⟩ := PoisonOr.bind_eq_value.mp h
    obtain rfl := PoisonOr.value_inj.mp h
    clear h
    simp [fieldsWidth, BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_eq_left]
    simp [unflatten_flatten hb, unflattenFields_flattenFields hbs]
end

end FlattenUnflatten

end MLIR.Ty

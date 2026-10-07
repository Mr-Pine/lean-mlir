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

def memberType : List Nat → Ty → Option Ty
  | [], t => some t
  | _, bv _ => none
  | _, ptr => none
  | [i], vec l w => if i < l then some (bv w) else none
  | _, vec .. => none
  | i :: is, array n t => if i < n then memberType is t else none
  | i :: is, struct fields => if h : i < fields.length then memberType is fields[i] else none

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
theorem unwrap_wrap_bv {v : ⟦bv w⟧ᵣ} : unwrap (wrap v) = .value v :=
  rfl

mutual
@[simp]
theorem unwrap_wrap {v : ⟦t⟧ᵣ} : unwrap (wrap v) = .value v := by
  cases t with
  | bv _ => exact unwrap_wrap_bv
  | ptr => simp [unwrap, wrap]
  | vec => simp [unwrap, wrap, PoisonOr.pure_def ▸ Vector.mapM_pure]
  | array =>
    simp [unwrap, wrap, Function.comp_def, unwrap_wrap, PoisonOr.pure_def ▸ Vector.mapM_pure]
  | struct => exact unwrapFields_wrapFields
@[simp]
theorem unwrapFields_wrapFields :
    ∀ {fs : List Ty} {v : denoteFieldsRaw fs}, unwrapFields (wrapFields v) = .value v
  | [], () => rfl
  | [_], _ => unwrap_wrap
  | _ :: _ :: _, (a, b) => by simp [unwrapFields, wrapFields, unwrap_wrap, unwrapFields_wrapFields]
end

mutual
theorem wrap_of_unwrap : ∀ {t : Ty} {v : ⟦t⟧} {r : ⟦t⟧ᵣ}, unwrap v = .value r → wrap r = v
  | bv _, _, _, h => by simp_all [wrap]
  | ptr, _, _, h => by simp_all [unwrap, wrap]
  | vec _ _, _, _, h => by
    simp only [unwrap, wrap] at h ⊢
    ext i hi
    simpa using (PoisonOr.vector_mapM_eq_value h i hi).symm
  | array _ _, _, _, h => by
    simp only [unwrap, wrap] at h ⊢
    ext i hi
    simpa using wrap_of_unwrap (PoisonOr.vector_mapM_eq_value h i hi)
  | struct _, _, _, h => wrapFields_of_unwrapFields h
theorem wrapFields_of_unwrapFields :
    ∀ {fs : List Ty} {v : denoteFields fs} {r : denoteFieldsRaw fs},
      unwrapFields v = .value r → wrapFields r = v
  | [], (), (), _ => rfl
  | [_], _, _, h => wrap_of_unwrap h
  | _ :: _ :: _, (_, _), (_, _), h => by
    simp only [unwrapFields, PoisonOr.bind_eq_value] at h
    obtain ⟨x, hx, xs, hxs, h⟩ := h
    simp only [PoisonOr.pure_def, PoisonOr.value_inj, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [wrapFields, wrap_of_unwrap hx, wrapFields_of_unwrapFields hxs]
end

end

public section

/-- The bits that round `n` up to a multiple of `a`. -/
@[expose]
def padding (n a : Nat) : Nat :=
  (a - n % a) % a

/-- The least power of two at least `n`. -/
@[expose]
def pow2Ceil (n : Nat) : Nat :=
  go n 1
where go : Nat → Nat → Nat
    | 0, p => p
    | k + 1, p => if n ≤ p then p else go k (2 * p)

mutual
/-- Alignment in bits, in LLVM's x86-64 data layout: an integer's is the least of `i8 … i128`'s
that fits it, a vector's its size up to a power of two. -/
@[expose]
def align : Ty → Nat
  | bv w =>
    if w ≤ 8 then 8 else if w ≤ 16 then 16 else if w ≤ 32 then 32 else if w ≤ 64 then 64 else 128
  | ptr => 64
  | vec l w => 8 * pow2Ceil ((w * l + 7) / 8)
  | array _ t => t.align
  | struct fields => fieldsAlign fields
@[expose]
def fieldsAlign : List Ty → Nat
  | [] => 8
  | t :: ts => max t.align (fieldsAlign ts)
end

mutual
/-- Width in bits in memory: array elements and struct fields padded as LLVM lays them out. -/
@[expose]
def width : Ty → Nat
  | bv w => w
  | ptr => 64
  | vec l w => w * l
  | array n t => (padding t.width t.align + t.width) * n
  | struct fields => fieldsWidth 0 (fieldsAlign fields) fields
/-- The width of fields `ts` from bit `off`, each followed by padding to the next one's offset, the
last to a multiple of `a`. -/
@[expose]
def fieldsWidth (off a : Nat) : List Ty → Nat
  | [] => 0
  | [t] => padding (off + t.width) a + t.width
  | t :: t' :: ts =>
    fieldsWidth (off + (padding (off + t.width) (max t.align t'.align) + t.width)) a (t' :: ts) +
      (padding (off + t.width) (max t.align t'.align) + t.width)
end

/-- The bits from one array element to the next: LLVM's allocation size. -/
@[expose]
def stride (t : Ty) : Nat :=
  padding t.width t.align + t.width

/-- The allocation size in bytes. -/
@[expose]
def size (t : Ty) : Nat :=
  t.stride / 8

/-- The bit offset of field `k` of fields `ts` from bit `off`. -/
@[expose]
def fieldOffset (off : Nat) : Nat → List Ty → Nat
  | k + 1, t :: t' :: ts =>
    fieldOffset (off + (padding (off + t.width) (max t.align t'.align) + t.width)) k (t' :: ts)
  | _, _ => off

mutual
@[expose]
def poisoned : (t : Ty) → ⟦t⟧
  | .bv _ | .ptr => PoisonOr.poison
  | .vec l _ => Vector.replicate l PoisonOr.poison
  | .array n t => Vector.replicate n (t.poisoned)
  | .struct fields => poisonedFields fields
@[expose]
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

theorem width_array : (array n t).width = t.stride * n :=
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

/-- A slice inside one lane of a packed bitvector is that lane's slice. -/
theorem _root_.BitVec.extractLsb'_packLanes_of_lt {we n : Nat} (v : Vector (BitVec we) n)
    {s w : Nat} (hi : s / we < n) (hw : s % we + w ≤ we) :
    (BitVec.packLanes v).extractLsb' s w = v[s / we].extractLsb' (s % we) w := by
  rw [← BitVec.extractLsb'_packLanes v (s / we) hi]
  ext k hk
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb']
  have := Nat.div_add_mod' s we
  simp only [show s % we + k < we by omega, decide_true, Bool.true_and]
  congr 1
  omega

end BitVecs

def allValues [Inhabited α] (v : Vector (PoisonOr α) n) : PoisonOr (Vector α n) :=
  if ∀ i : Fin n, v[i].isPoison = false then .value (Vector.ofFn fun i => v[i].getValue)
  else .poison

mutual
/-- A value's bits, with zero padding. -/
def flattenRaw : (t : Ty) → ⟦t⟧ᵣ → BitVec t.width
  | bv _, x => x
  | ptr, _ => 0#_
  | vec _ _, v => BitVec.packLanes v
  | array _ t, v => BitVec.packLanes (v.map fun x => 0#(padding t.width t.align) ++ flattenRaw t x)
  | struct fields, v => flattenRawFields 0 (fieldsAlign fields) fields v
def flattenRawFields (off a : Nat) :
    (ts : List Ty) → denoteFieldsRaw ts → BitVec (fieldsWidth off a ts)
  | [], _ => 0#0
  | [t], v => 0#(padding (off + t.width) a) ++ flattenRaw t v
  | t :: t' :: ts, (x, xs) =>
    flattenRawFields (off + (padding (off + t.width) (max t.align t'.align) + t.width)) a (t' :: ts)
        xs ++
      (0#(padding (off + t.width) (max t.align t'.align)) ++ flattenRaw t x)
end

theorem flattenRaw_bv (x : ⟦bv w⟧ᵣ) : flattenRaw (bv w) x = x := by rfl

theorem flattenRaw_vec (v : ⟦vec l w⟧ᵣ) : flattenRaw (vec l w) v = BitVec.packLanes v := by rfl

theorem flattenRaw_array (v : ⟦array n t⟧ᵣ) :
    flattenRaw (array n t) v =
      BitVec.packLanes (v.map fun x => 0#(padding t.width t.align) ++ flattenRaw t x) := by
  rfl

theorem flattenRaw_struct (v : ⟦struct fs⟧ᵣ) :
    flattenRaw (struct fs) v = flattenRawFields 0 (fieldsAlign fs) fs v := by rfl

theorem flattenRawFields_singleton (v : denoteFieldsRaw [t]) :
    flattenRawFields off a [t] v = 0#(padding (off + t.width) a) ++ flattenRaw t v := by rfl

theorem flattenRawFields_cons (x : ⟦t⟧ᵣ) (xs : denoteFieldsRaw (t' :: ts)) :
    flattenRawFields off a (t :: t' :: ts) (x, xs) =
      flattenRawFields (off + (padding (off + t.width) (max t.align t'.align) + t.width)) a
          (t' :: ts) xs ++
        (0#(padding (off + t.width) (max t.align t'.align)) ++ flattenRaw t x) := by
  rfl

/-- A raw value's bits at its width `w`, a literal: what a global's block holds. -/
def flatBits {t : Ty} (r : ⟦t⟧ᵣ) {w : Nat} {hw : t.width = w} : BitVec w :=
  (t.flattenRaw r).cast hw

theorem flatBits_eq {r : ⟦t⟧ᵣ} {hw : t.width = w} :
    flatBits r (hw := hw) = (t.flattenRaw r).cast hw := by rfl

/-- A slice of an array's bits inside one element is that element's slice. -/
theorem extractLsb'_flattenRaw_array (v : ⟦array n t⟧ᵣ) (hi : s / t.stride < n)
    (hw : s % t.stride + w ≤ t.width) :
    (flattenRaw (array n t) v).extractLsb' s w =
      (flattenRaw t (v[s / t.stride]'hi)).extractLsb' (s % t.stride) w := by
  unfold stride at hi hw ⊢
  refine (BitVec.extractLsb'_packLanes_of_lt _ hi (by omega)).trans ?_
  rw [Vector.getElem_map]
  exact BitVec.extractLsb'_append_eq_of_add_le hw

theorem extractLsb'_flattenRaw_struct_singleton (v : ⟦struct [t]⟧ᵣ) (hw : s + w ≤ t.width) :
    (flattenRaw (struct [t]) v).extractLsb' s w = (flattenRaw t v).extractLsb' s w :=
  BitVec.extractLsb'_append_eq_of_add_le hw

theorem extractLsb'_flattenRaw_bv (x : ⟦bv l⟧ᵣ) :
    (flattenRaw (bv l) x).extractLsb' s w = x.extractLsb' s w := by rfl

@[expose, simp]
def hasPtr : Ty → Bool
  | ptr => true
  | bv _ | vec _ _ => false
  | array _ t => t.hasPtr
  | struct fs => fs.attach.any fun ⟨t, _⟩ => t.hasPtr -- or a mutual hasPtrFields

theorem hasPtr_bv : (bv w).hasPtr = false := by simp [hasPtr]

theorem hasPtr_array : (array n t).hasPtr = t.hasPtr := by simp [hasPtr]

theorem hasPtr_struct0 : (struct []).hasPtr = false := by simp [hasPtr]

theorem hasPtr_struct : (struct (t :: ts)).hasPtr = (t.hasPtr || (struct ts).hasPtr) := by
  simp [hasPtr]

def flatten (t : Ty) (v : ⟦t⟧) : PoisonOr (BitVec t.width) := do
  let unwrapped ← t.unwrap v
  if hasPtr t then
    .poison
  return flattenRaw t unwrapped

theorem flatten_wrap (h : t.hasPtr = false) : flatten t (wrap v) = .value (flattenRaw t v) := by
  simp [flatten, h]

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
  | array n t, x =>
    Vector.ofFn fun i =>
      unflatten t ((extractVecElem n (padding t.width t.align + t.width) i x).extractLsb' 0 t.width)
  | struct fields, x => unflattenFields 0 (fieldsAlign fields) fields x
def unflattenFields (off a : Nat) : (ts : List Ty) → BitVec (fieldsWidth off a ts) → denoteFields ts
  | [], _ => ()
  | [t], x => unflatten t (x.extractLsb' 0 t.width)
  | t :: t' :: ts, x =>
    let w := padding (off + t.width) (max t.align t'.align) + t.width
    let v := x.extractLsb' 0 t.width
    let vs := x.extractLsb' w (fieldsWidth (off + w) a (t' :: ts))
    (unflatten t v, unflattenFields (off + w) a (t' :: ts) vs)
end

@[simp]
theorem flatten_bv (x : ⟦bv w⟧) : flatten (bv w) x = x := by
  simp [flatten, hasPtr]
  cases h : x using PoisonOr.casesOn' <;> simp [flattenRaw]

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
  simp [flatten, hasPtr]
  congr

@[simp]
theorem flatten_ptr (x : ⟦ptr⟧) : flatten ptr x = .poison := by simp [flatten, hasPtr]

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
theorem unflatten_flattenRaw {t : Ty} {v : ⟦t⟧ᵣ} {b : BitVec t.width} (hnoptr : t.hasPtr = false)
    (h : flattenRaw t v = b) : unflatten t b = Ty.wrap v := by
  cases t with
  | bv w =>
    cases v; simp_all [flattenRaw, unflatten, wrap]
  | ptr => simp [hasPtr] at hnoptr
  | vec l w =>
    simp_all [flattenRaw, unflatten, denote, ← h, extractVecElem_packLanes, wrap]
    ext i hi
    simp
  | array n t =>
    simp_all [flattenRaw, unflatten, denote, ← h, extractVecElem_packLanes, wrap]
    ext i hi
    simp
    rw [unflatten_flattenRaw (by simpa [hasPtr] using hnoptr)
        BitVec.extractLsb'_append_eq_right.symm]
  | struct fields => exact unflattenRawFields_flattenRawFields (by simpa [hasPtr] using hnoptr) h
theorem unflattenRawFields_flattenRawFields (hnoptr : ∀ t ∈ ts, t.hasPtr = false)
    (h : flattenRawFields off a ts v = b) : unflattenFields off a ts b = wrapFields v :=
  match ts with
  | [] => by simp [unflattenFields]
  | [t] => by
    simp [unflattenFields, wrapFields]
    subst h
    rw [flattenRawFields_singleton]
    exact unflatten_flattenRaw (by simp [hnoptr]) BitVec.extractLsb'_append_eq_right.symm
  | t₁ :: t₂ :: ts => by
    simp [unflattenFields, wrapFields, flattenRawFields] at ⊢ h
    subst h
    constructor
    · refine unflatten_flattenRaw (hnoptr t₁ (by simp)) ?_
      -- the field, under its padding and the later fields
      refine
        ((BitVec.extractLsb'_append_eq_of_add_le ?_).trans BitVec.extractLsb'_append_eq_right).symm
      omega
    · exact
        unflattenRawFields_flattenRawFields (by simp_all) (BitVec.extractLsb'_append_eq_left).symm
end

theorem unflatten_flatten {t : Ty} {v : ⟦t⟧} {b : BitVec t.width} (h : flatten t v = .value b) :
    unflatten t b = v := by
  simp only [flatten, PoisonOr.bind_eq_value] at h
  obtain ⟨r, hr, h⟩ := h
  cases hp : t.hasPtr
  · simp [hp] at h
    rw [unflatten_flattenRaw hp h, wrap_of_unwrap hr]
  · simp [hp] at h
    exact absurd h (PoisonOr.poison_ne_value b)

end FlattenUnflatten

end MLIR.Ty

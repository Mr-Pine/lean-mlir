module

public import MLIR.Semantics.Operations.Scalar

namespace MLIR.Operation

@[expose] public section

mutual
def insert :
    {tCont tVal : Ty} →
      (indices : List Nat) → tCont.memberType indices == some tVal → ⟦tCont⟧ → ⟦tVal⟧ → ⟦tCont⟧
  | tVal, tCont, [], h, _, val =>
    have : tVal = tCont := by
      simp [Ty.memberType] at h
      simp [h]
    this ▸ val
  | .bv _, _, t :: ts, h, _, _ | .ptr, _, t :: ts, h, _, _ => by simp [Ty.memberType] at h
  | .vec l w, tVal, [i], h, vec, elem =>
    let vec : Vector _ _ := vec
    have : ⟦tVal⟧ = PoisonOr (BitVec w) := by
      simp [Ty.memberType] at h
      simp [← h.right]
    let elem := this ▸ elem
    vec.set i elem (h := by
      simp [Ty.memberType] at h; exact h.left)
  | .vec _ _, tVal, i₁ :: i₂ :: is, h, _, _ => by simp [Ty.memberType] at h
  | .array n t, tVal, i :: is, h, arr, elem =>
    let arr : Vector _ _ := arr
    let currentMember :=
      arr.get
        ⟨i, by
          simp [Ty.memberType] at h; simp [h]⟩
    let newMember :=
      insert (tCont := t) (tVal := tVal) is
        (by
          simp [Ty.memberType] at h; simp [h])
        currentMember elem
    arr.set i newMember (h := by
      simp [Ty.memberType] at h; exact h.left)
  | .struct fields, tVal, i :: is, h, str, val =>
    have hi : i < fields.length := by
      simp [Ty.memberType] at h
      exact h.1
    have h : (fields[i]).memberType is == some tVal := by
      simp [Ty.memberType] at h
      simp [h.2]
    insertField i is hi h str val
def insertField :
    {ts : List Ty} →
      {tVal : Ty} →
      (i : Nat) →
      (is : List Nat) →
      (hi : i < ts.length) →
      ts[i].memberType is == some tVal → Ty.denoteFields ts → ⟦tVal⟧ → Ty.denoteFields ts
  | [_], _, 0, is, _, h, v, elem => insert is h v elem
  | _ :: _ :: _, _, 0, is, _, h, (a, b), elem => (insert is h a elem, b)
  | _ :: _ :: _, _, i + 1, is, hi, h, (a, b), elem =>
    (a,
      insertField i is
        (by
          simp at ⊢ hi; exact hi)
        h b elem)
  | [], _, _, _, hi, _, _, _ => absurd hi (by simp)
  | [_], _, _ + 1, _, hi, _, _, _ => absurd hi (by simp)
end

mutual
/-- The member of `cont` at `indices`. -/
def extract :
    {tCont tVal : Ty} →
      (indices : List Nat) → tCont.memberType indices == some tVal → ⟦tCont⟧ → ⟦tVal⟧
  | tCont, tVal, [], h, cont =>
    have : tCont = tVal := by
      simp [Ty.memberType] at h
      simp [h]
    this ▸ cont
  | .bv _, _, _ :: _, h, _ | .ptr, _, _ :: _, h, _ => by simp [Ty.memberType] at h
  | .vec l w, tVal, [i], h, vec =>
    let vec : Vector _ _ := vec
    have : PoisonOr (BitVec w) = ⟦tVal⟧ := by
      simp [Ty.memberType] at h
      simp [← h.right]
    this ▸
      vec[i]'(by
          simp [Ty.memberType] at h; exact h.left)
  | .vec _ _, _, _ :: _ :: _, h, _ => by simp [Ty.memberType] at h
  | .array n t, tVal, i :: is, h, arr =>
    let arr : Vector _ _ := arr
    extract (tCont := t) (tVal := tVal) is
      (by
        simp [Ty.memberType] at h; simp [h])
      (arr[i]'(by
          simp [Ty.memberType] at h; exact h.left))
  | .struct fields, tVal, i :: is, h, str =>
    have hi : i < fields.length := by
      simp [Ty.memberType] at h
      exact h.1
    have h : (fields[i]).memberType is == some tVal := by
      simp [Ty.memberType] at h
      simp [h.2]
    extractField i is hi h str
/-- The member at `is` of field `i` of `str`. -/
def extractField :
    {ts : List Ty} →
      {tVal : Ty} →
      (i : Nat) →
      (is : List Nat) →
      (hi : i < ts.length) → ts[i].memberType is == some tVal → Ty.denoteFields ts → ⟦tVal⟧
  | [_], _, 0, is, _, h, str => extract is h str
  | _ :: _ :: _, _, 0, is, _, h, str => extract is h str.1
  | _ :: _ :: _, _, i + 1, is, hi, h, str =>
    extractField i is
      (by
        simp at ⊢ hi; exact hi)
      h str.2
  | [], _, _, _, hi, _, _ => absurd hi (by simp)
  | [_], _, _ + 1, _, hi, _, _ => absurd hi (by simp)
end

attribute [mlir_operation] extract extractField

def insertvalue (indices : List Nat) (tCont tVal : Ty) (h : tCont.memberType indices == some tVal)
    (cont : ⟦tCont⟧) (val : ⟦tVal⟧) : ⟦tCont⟧ :=
  insert indices h cont val

/-- `llvm.extractvalue`: the member of `cont` at `indices`. -/
@[mlir_operation]
def extractvalue (indices : List Nat) (tCont tVal : Ty) (h : tCont.memberType indices == some tVal)
    (cont : ⟦tCont⟧) : ⟦tVal⟧ :=
  extract indices h cont

end

end MLIR.Operation

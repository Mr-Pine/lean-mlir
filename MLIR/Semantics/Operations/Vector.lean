module

public import MLIR.Semantics.Operations.Scalar

namespace MLIR.Operation

@[expose] public section

/-- `llvm.extractelement`: lane `idx` of `v`; poison if `idx` is poison or out of range. -/
@[mlir_operation]
def extractelement {l w wi : Nat} (v : ⟦.vec l w⟧) (idx : IntW wi) : IntW w :=
  match idx with
  | .value i => if h : i.toNat < l then v[i.toNat] else .poison
  | .poison => .poison

/-- `llvm.insertelement`: `v` with lane `idx` set to `x`; all poison if `idx` is poison or out of
range. -/
@[mlir_operation]
def insertelement {l w wi : Nat} (v : ⟦.vec l w⟧) (x : IntW w) (idx : IntW wi) : ⟦.vec l w⟧ :=
  match idx with
  | .value i => if h : i.toNat < l then v.set i.toNat x h else (Ty.vec l w).poisoned
  | .poison => (Ty.vec l w).poisoned

@[mlir_operation]
def shufflevector {l w : Nat} (indices : Vector (Option (Fin (2 * l))) l) (a b : ⟦.vec l w⟧) :
    ⟦.vec l w⟧ :=
  Vector.ofFn (n := l)
    (fun i => do
      let some idx := indices[i] | .poison
      if h : idx < l then
        a[idx]'h
      else
        b[idx - l])

@[mlir_operation]
def vpermi2var {l w : Nat} (a idx b : ⟦.vec l w⟧) : ⟦.vec l w⟧ :=
  Vector.ofFn (n := l)
    (fun i => do
      let j ← idx[i]
      let idx := j.toNat % (2 * l)
      have : idx < 2 * l :=
        Nat.mod_lt _
          (by
            have := i.pos; omega)
      if h : idx < l then
        a[idx]'h
      else
        b[idx - l])

/-- `vpmadd52luq`: lane `i` is `a[i]` plus the low 52 bits of the product of `b[i]`'s and `c[i]`'s
low 52 bits. -/
@[mlir_operation]
def vpmadd52l {l : Nat} (a b c : ⟦.vec l 64⟧) : ⟦.vec l 64⟧ :=
  Vector.ofFn (n := l) fun i => do
    let x ← a[i]
    let y ← b[i]
    let z ← c[i]
    let m : BitVec 64 := 0xFFFFFFFFFFFFF
    return x + ((y &&& m) * (z &&& m) &&& m)

/-- `vpmadd52huq`: lane `i` is `a[i]` plus the high 52 bits of the 104-bit product of `b[i]`'s and
`c[i]`'s low 52 bits. -/
@[mlir_operation]
def vpmadd52h {l : Nat} (a b c : ⟦.vec l 64⟧) : ⟦.vec l 64⟧ :=
  Vector.ofFn (n := l) fun i => do
    let x ← a[i]
    let y ← b[i]
    let z ← c[i]
    let m : BitVec 64 := 0xFFFFFFFFFFFFF
    return x + (((y &&& m).setWidth 128 * (z &&& m).setWidth 128) >>> 52).setWidth 64

end

end MLIR.Operation

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

/-- `llvm.shufflevector`: lane `i` is `a[k]` or `b[k - l₁]` for mask entry `some k`, else poison.
Not `mlir_operation`: `unfoldShufflevector` unfolds it only for a closed mask. -/
def shufflevector {l₁ l₂ w : Nat} (indices : Vector (Option (Fin (2 * l₁))) l₂)
    (a b : ⟦.vec l₁ w⟧) : ⟦.vec l₂ w⟧ :=
  Vector.ofFn (n := l₂)
    (fun i => do
      let some idx := indices[i] | .poison
      if h : idx < l₁ then
        a[idx]'h
      else
        b[idx - l₁])

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

/-- `llvm.x86.avx2.pblendvb`: lane `i` is `b[i]` if `mask[i]`'s top bit is set, else `a[i]`; poison
if `mask[i]` is. InstCombine's `select (icmp slt mask 0) b a`, lane-wise. -/
@[mlir_operation]
def pblendvb {l : Nat} (a b mask : ⟦.vec l 8⟧) : ⟦.vec l 8⟧ :=
  Vector.ofFn (n := l) fun i => do
    let m ← mask[i]
    if m.msb then
      b[i]
    else
      a[i]

/-- The OR of lanes `0` to `n` of `v`; poison if one is. -/
@[mlir_operation]
def orLanes {l w : Nat} (v : ⟦.vec l w⟧) : (n : Nat) → n < l → IntW w
  | 0, _ => v[0]
  | n + 1, h => do
    let x ← orLanes v n (by omega)
    let y ← v[n + 1]
    return x ||| y

/-- `llvm.intr.vector.reduce.or`: the OR of `v`'s lanes; poison if one is. -/
@[mlir_operation]
def reduceOr {l w : Nat} (v : ⟦.vec l w⟧) : IntW w :=
  match l, v with
  | 0, _ => .value 0
  | n + 1, v => orLanes v n (by omega)

/-- The AND of lanes `0` to `n` of `v`; poison if one is. -/
@[mlir_operation]
def andLanes {l w : Nat} (v : ⟦.vec l w⟧) : (n : Nat) → n < l → IntW w
  | 0, _ => v[0]
  | n + 1, h => do
    let x ← andLanes v n (by omega)
    let y ← v[n + 1]
    return x &&& y

/-- `llvm.intr.vector.reduce.and`: the AND of `v`'s lanes; poison if one is. -/
@[mlir_operation]
def reduceAnd {l w : Nat} (v : ⟦.vec l w⟧) : IntW w :=
  match l, v with
  | 0, _ => .value (BitVec.allOnes w)
  | n + 1, v => andLanes v n (by omega)

/-- The wrapping sum of lanes `0` to `n` of `v`; poison if one is. -/
@[mlir_operation]
def addLanes {l w : Nat} (v : ⟦.vec l w⟧) : (n : Nat) → n < l → IntW w
  | 0, _ => v[0]
  | n + 1, h => do
    let x ← addLanes v n (by omega)
    let y ← v[n + 1]
    return x + y

/-- `llvm.intr.vector.reduce.add`: the wrapping sum of `v`'s lanes; poison if one is. -/
@[mlir_operation]
def reduceAdd {l w : Nat} (v : ⟦.vec l w⟧) : IntW w :=
  match l, v with
  | 0, _ => .value 0
  | n + 1, v => addLanes v n (by omega)

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

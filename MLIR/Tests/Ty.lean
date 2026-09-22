module

import MLIR.Ty
meta import MLIR.Ty

/-! # `Ty`: widths, denotations, flattening -/

namespace MLIR.Tests

open Ty

#guard (Ty.bv 64).width == 64

#guard (Ty.bv 1).width == 1

#guard Ty.ptr.width == 64

-- `decide` on types works downstream (needs the derived instance to be exposed)
example : Ty.bv 3 ≠ Ty.ptr := by decide

example : Ty.bv 3 ≠ Ty.bv 4 := by decide

-- `⟦·⟧` reduces, and `denote` is reducible enough for a plain ascription
example (x : ⟦Ty.bv 8⟧) : PoisonOr (BitVec 8) :=
  x

example (p : ⟦Ty.ptr⟧) : PoisonOr Pointer :=
  p

-- `poisoned`
#guard (Ty.poisoned (.bv 8)).isPoison

#guard (Ty.poisoned .ptr).isPoison

example : Ty.poisoned (.bv 8) = (.poison : PoisonOr (BitVec 8)) := by simp

/-! ## flatten / unflatten -/

#guard Ty.flatten (.bv 8) (.value 0xab#8) == PoisonOr.value 0xab#8

#guard (Ty.flatten (.bv 8) .poison).isPoison

-- a pointer has no bit pattern, so it cannot be flattened
#guard (Ty.flatten .ptr (.value ⟨⟨0⟩, 0⟩)).isPoison

#guard Ty.unflatten (.bv 8) 0xab#8 == PoisonOr.value 0xab#8

#guard (Ty.unflatten .ptr 0#64).isPoison

-- round trip on values
example (x : BitVec 16) : Ty.unflatten (.bv 16) x = .value x := by simp

-- NOTE: `simp` alone leaves `value x = value x` here, because the two sides' implicit type
-- arguments differ syntactically (`⟦bv 16⟧`'s inner match vs `BitVec 16`); `rfl` closes it.
example (x : BitVec 16) : Ty.flatten (.bv 16) (.value x) = .value x :=
  Ty.flatten_bv _

end MLIR.Tests

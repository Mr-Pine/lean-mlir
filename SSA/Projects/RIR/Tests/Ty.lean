module

import SSA.Projects.RIR.Ty
meta import SSA.Projects.RIR.Ty

/-! # `Ty`: widths, denotations, flattening -/

namespace LeanMLIR.RIR.Tests

open Ty

#guard (Ty.bv 64).width == 64

#guard (Ty.bv 1).width == 1

#guard Ty.ptr.width == 64

/-! ## Layout: LLVM's x86-64 padding -/

-- the `i64` at byte 8, and 7 bytes of padding before it
#guard (Ty.struct [.bv 8, .bv 64]).width == 128

#guard Ty.fieldOffset 0 1 [.bv 8, .bv 64] == 64

-- tail padding up to the struct's alignment
#guard (Ty.struct [.bv 64, .bv 8]).width == 128

#guard (List.range 3).map (Ty.fieldOffset 0 · [.bv 32, .bv 8, .bv 16]) == [0, 32, 48]

#guard (Ty.struct [.bv 32, .bv 8, .bv 16]).width == 64

-- an element's allocation size, not its store size: `i24` takes 4 bytes, `<3 x i32>` 16
#guard Ty.fieldOffset 0 1 [.bv 24, .bv 8] == 32

#guard (Ty.vec 3 32).size == 16

#guard (Ty.array 2 (.struct [.bv 64, .bv 8])).width == 256

#guard (Ty.array 4 (.bv 1)).width == 32

-- naturally aligned structs need no padding
#guard
  (Ty.struct
        [.array 128 (.bv 8), .array 8 (.bv 64), .bv 64, .bv 64, .bv 64, .bv 64,
          .array 32 (.bv 8)]).size ==
    256

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

end LeanMLIR.RIR.Tests

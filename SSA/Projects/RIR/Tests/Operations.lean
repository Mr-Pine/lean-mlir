module

import SSA.Projects.RIR.Semantics.Operations.Scalar
import SSA.Projects.RIR.Memory.Range
meta import SSA.Projects.RIR.Semantics.Operations.Scalar
meta import SSA.Projects.RIR.Memory.Range

/-! # Scalar operations and range disjointness -/

namespace LeanMLIR.RIR.Tests

open Operation

/-! ## `and` -/

#guard and (.value 0b1100#4) (.value 0b1010#4) == PoisonOr.value 0b1000#4

#guard (and (.value 0b1100#4) .poison).isPoison

#guard (and .poison (.value 0b1010#4)).isPoison

/-! ## `smin` — signed, so a negative operand wins -/

#guard smin (.value 3#32) (.value 14#32) == PoisonOr.value 3#32

#guard smin (.value 20#32) (.value 14#32) == PoisonOr.value 14#32

#guard smin (.value (-5 : BitVec 32)) (.value 14#32) == PoisonOr.value (-5 : BitVec 32)

#guard
  smin (.value (-2147483648 : BitVec 32)) (.value 0#32) == PoisonOr.value (-2147483648 : BitVec 32)

#guard (smin (.value 3#32) .poison).isPoison

/-! ## `icmp` -/

#guard icmp .eq (.value 3#8) (.value 3#8) == PoisonOr.value 1#1

#guard icmp .eq (.value 3#8) (.value 4#8) == PoisonOr.value 0#1

#guard icmp .ne (.value 3#8) (.value 4#8) == PoisonOr.value 1#1

#guard icmp .ne (.value 3#8) (.value 3#8) == PoisonOr.value 0#1

#guard (icmp .eq (.value 3#8) .poison).isPoison

/-! ## `select` — LLVM's orientation: the condition being *true* picks the first value -/

#guard select (τ := .bv 8) (.value 1#1) (.value 11#8) (.value 22#8) == PoisonOr.value 11#8

#guard select (τ := .bv 8) (.value 0#1) (.value 11#8) (.value 22#8) == PoisonOr.value 22#8

#guard (select (τ := .bv 8) .poison (.value 11#8) (.value 22#8)).isPoison

-- the unselected operand may be poison without poisoning the result
#guard select (τ := .bv 8) (.value 1#1) (.value 11#8) .poison == PoisonOr.value 11#8

#guard (select (τ := .bv 8) (.value 1#1) .poison (.value 22#8)).isPoison

/-! ## `constant` -/

#guard constant 0xab#8 == PoisonOr.value 0xab#8

/-! ## `Range.Disjoint` (offsets and widths in bits) -/

private def r (id off w : Nat) : Range :=
  ⟨⟨id⟩, off, w⟩

-- different blocks are disjoint whatever the offsets
#guard decide ((r 0 0 64).Disjoint (r 1 0 64))

-- adjacent ranges in one block are disjoint; overlapping ones are not
#guard decide ((r 0 0 8).Disjoint (r 0 8 8))

#guard decide ((r 0 8 8).Disjoint (r 0 0 8))

#guard !decide ((r 0 0 16).Disjoint (r 0 8 8))

#guard !decide ((r 0 0 64).Disjoint (r 0 0 64))

-- NOTE: a zero-width range *inside* another is NOT disjoint under the current definition
-- (`8 + 0 ≤ 0` and `8 ≥ 0 + 64` both fail). It touches no bytes, so arguably it should be.
-- This only matters once an operation can have width 0 — `memset`/`memcpy` with length 0.
#guard !decide ((r 0 8 0).Disjoint (r 0 0 64))

-- outside, it is disjoint
#guard decide ((r 0 64 0).Disjoint (r 0 0 64))

end LeanMLIR.RIR.Tests

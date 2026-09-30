module

import MLIR.Semantics.Operations.Scalar
import MLIR.Semantics.Operations.Vector
import MLIR.Memory.Range
meta import MLIR.Semantics.Operations.Scalar
meta import MLIR.Semantics.Operations.Vector
meta import MLIR.Memory.Range

/-! # Scalar operations and range disjointness -/

namespace MLIR.Tests

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

/-! ## `or`, `xor` — `disjoint` makes shared bits poison -/

#guard or false (.value 0b1100#4) (.value 0b1010#4) == PoisonOr.value 0b1110#4

#guard (or true (.value 0b1100#4) (.value 0b1010#4)).isPoison

#guard or true (.value 0b1100#4) (.value 0b0011#4) == PoisonOr.value 0b1111#4

#guard xor (.value 0b1100#4) (.value 0b1010#4) == PoisonOr.value 0b0110#4

/-! ## `icmp` orders: signed and unsigned read `-1` differently -/

#guard icmp .slt (.value (-1 : BitVec 8)) (.value 0#8) == PoisonOr.value 1#1

#guard icmp .ult (.value (-1 : BitVec 8)) (.value 0#8) == PoisonOr.value 0#1

#guard icmp .sgt (.value 0#8) (.value (-1 : BitVec 8)) == PoisonOr.value 1#1

#guard icmp .ugt (.value (-1 : BitVec 8)) (.value 0#8) == PoisonOr.value 1#1

#guard icmp .sle (.value 5#8) (.value 5#8) == PoisonOr.value 1#1

#guard icmp .sge (.value (-2 : BitVec 8)) (.value (-1 : BitVec 8)) == PoisonOr.value 0#1

#guard icmp .ule (.value 6#8) (.value 5#8) == PoisonOr.value 0#1

#guard icmp .uge (.value 5#8) (.value 5#8) == PoisonOr.value 1#1

/-! ## `sext` — the sign bit fills the new high bits -/

#guard sext (w' := 16) (.value 0x7F#8) == PoisonOr.value 0x007F#16

#guard sext (w' := 16) (.value 0x80#8) == PoisonOr.value 0xFF80#16

-- `i1` to `i8`, as `ge_decode2` uses it: true is all ones
#guard sext (w' := 8) (.value 1#1) == PoisonOr.value 0xFF#8

#guard sext (w' := 8) (.value 0#1) == PoisonOr.value 0#8

#guard (sext (w' := 8) (.poison : IntW 1)).isPoison

/-! ## `fshl`, `fshr` — shifts of `x ++ y`, by the amount mod the width -/

#guard fshl (.value 0x12#8) (.value 0x34#8) (.value 4#8) == PoisonOr.value 0x23#8

#guard fshl (.value 0x12#8) (.value 0x34#8) (.value 12#8) == PoisonOr.value 0x23#8

#guard fshl (.value 0x12#8) (.value 0x34#8) (.value 0#8) == PoisonOr.value 0x12#8

#guard fshr (.value 0x12#8) (.value 0x34#8) (.value 4#8) == PoisonOr.value 0x23#8

#guard fshr (.value 0x12#8) (.value 0x34#8) (.value 0#8) == PoisonOr.value 0x34#8

#guard (fshl (.value 0x12#8) (.value 0x34#8) .poison).isPoison

/-! ## `bswap` -/

#guard bswap (.value 0x12345678#32) == PoisonOr.value 0x78563412#32

#guard bswap (.value 0x0102030405060708#64) == PoisonOr.value 0x0807060504030201#64

/-! ## `bitcast` — lane 0 is the low bits; poison stays in its lanes, but poisons a whole scalar -/

#guard
  bitcast (t := .bv 8) (t' := .vec 8 1) rfl (.value 0b101#8) ==
    (#v[.value 1#1, .value 0#1, .value 1#1, .value 0#1, .value 0#1, .value 0#1, .value 0#1,
        .value 0#1] :
      ⟦Ty.vec 8 1⟧)

#guard
  bitcast (t := .vec 8 1) (t' := .bv 8) rfl
      #v[.value 1#1, .value 0#1, .value 1#1, .value 0#1, .value 0#1, .value 0#1, .value 0#1,
        .value 0#1] ==
    PoisonOr.value 0b101#8

#guard (bitcast (t := .vec 2 4) (t' := .bv 8) rfl #v[.value 1#4, .poison] : ⟦Ty.bv 8⟧).isPoison

-- between vectors, only the result lanes overlapping a poison lane are poison
#guard
  bitcast (t := .vec 2 8) (t' := .vec 4 4) rfl #v[.value 0x21#8, .poison] ==
    (#v[.value 1#4, .value 2#4, .poison, .poison] : ⟦Ty.vec 4 4⟧)

#guard
  bitcast (t := .vec 4 4) (t' := .vec 2 8) rfl #v[.value 1#4, .value 2#4, .value 3#4, .poison] ==
    (#v[.value 0x21#8, .poison] : ⟦Ty.vec 2 8⟧)

/-! ## `insertelement`, `extractelement` — a bad or poison index is poison -/

#guard
  insertelement (#v[.value 1#8, .value 2#8, .value 3#8] : ⟦Ty.vec 3 8⟧) (.value 9#8)
      (.value 1#32) ==
    #v[.value 1#8, .value 9#8, .value 3#8]

#guard
  insertelement (#v[.value 1#8, .value 2#8, .value 3#8] : ⟦Ty.vec 3 8⟧) .poison (.value 0#32) ==
    #v[.poison, .value 2#8, .value 3#8]

#guard
  insertelement (#v[.value 1#8, .value 2#8, .value 3#8] : ⟦Ty.vec 3 8⟧) (.value 9#8)
      (.value 3#32) ==
    Ty.poisoned (.vec 3 8)

#guard
  insertelement (#v[.value 1#8, .value 2#8, .value 3#8] : ⟦Ty.vec 3 8⟧) (.value 9#8)
      (.poison : IntW 32) ==
    Ty.poisoned (.vec 3 8)

#guard
  extractelement (#v[.value 1#8, .value 2#8, .value 3#8] : ⟦Ty.vec 3 8⟧) (.value 2#64) ==
    PoisonOr.value 3#8

#guard
  (extractelement (#v[.value 1#8, .value 2#8, .value 3#8] : ⟦Ty.vec 3 8⟧) (.value 3#64)).isPoison

#guard
  (extractelement (#v[.value 1#8, .value 2#8, .value 3#8] : ⟦Ty.vec 3 8⟧)
      (.poison : IntW 64)).isPoison

/-! ## `shufflevector` — indices past the first operand read the second; `none` is poison -/

-- widening: two 2-lane operands into 4 lanes
#guard
  shufflevector (#v[some 0, some 3, none, some 1] : Vector (Option (Fin (2 * 2))) 4)
      (#v[.value 1#8, .value 2#8] : ⟦Ty.vec 2 8⟧) #v[.value 3#8, .value 4#8] ==
    (#v[.value 1#8, .value 4#8, .poison, .value 2#8] : ⟦Ty.vec 4 8⟧)

-- narrowing: two 4-lane operands into 2 lanes
#guard
  shufflevector (#v[some 7, some 0] : Vector (Option (Fin (2 * 4))) 2)
      (#v[.value 1#8, .value 2#8, .value 3#8, .value 4#8] : ⟦Ty.vec 4 8⟧)
      #v[.value 5#8, .value 6#8, .value 7#8, .value 8#8] ==
    (#v[.value 8#8, .value 1#8] : ⟦Ty.vec 2 8⟧)

-- a poison lane is only read where selected
#guard
  shufflevector (#v[some 1, some 1] : Vector (Option (Fin (2 * 2))) 2)
      (#v[.poison, .value 2#8] : ⟦Ty.vec 2 8⟧) #v[.value 3#8, .value 4#8] ==
    (#v[.value 2#8, .value 2#8] : ⟦Ty.vec 2 8⟧)

/-! ## `vpmadd52h` — the high half of the 104-bit product, of the low 52 bits -/

#guard
  vpmadd52h (#v[.value 1] : ⟦Ty.vec 1 64⟧) #v[.value (2 ^ 51)] #v[.value (2 ^ 51)] ==
    #v[.value (1 + 2 ^ 50)]

#guard
  vpmadd52h (#v[.value 1] : ⟦Ty.vec 1 64⟧) #v[.value (2 ^ 52 + 2 ^ 51)] #v[.value (2 ^ 51)] ==
    #v[.value (1 + 2 ^ 50)]

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

end MLIR.Tests

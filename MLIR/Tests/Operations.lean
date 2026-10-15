module

import MLIR.Semantics.Operations.Scalar
import MLIR.Semantics.Operations.Vector
import MLIR.Semantics.Operations.Container
import MLIR.Memory.Range
meta import MLIR.Semantics.Operations.Scalar
meta import MLIR.Semantics.Operations.Vector
meta import MLIR.Semantics.Operations.Container
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

/-! ## `cttz` -/

#guard cttz false (.value 0b101000#8) == PoisonOr.value 3#8

#guard cttz false (.value 0#64) == PoisonOr.value 64#64

#guard (cttz true (.value 0#64)).isPoison

#guard cttz true (.value 0x8000000000000000#64) == PoisonOr.value 63#64

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

/-! ## `vpmadd52l` — the low half of the product, of the low 52 bits -/

#guard
  vpmadd52l (#v[.value 1, .value 0, .poison, .value 0] : ⟦Ty.vec 4 64⟧)
      #v[.value (2 ^ 52 + 3), .value (2 ^ 51), .value 1, .value 1]
      #v[.value 5, .value 4, .value 1, .poison] ==
    #v[.value 16, .value 0, .poison, .poison]

/-! ## `pblendvb` — the mask's top bit picks `b`; a poison mask lane is poison -/

#guard
  pblendvb (#v[.value 1, .value 2, .value 3, .value 4] : ⟦Ty.vec 4 8⟧)
      #v[.value 11, .value 12, .value 13, .value 14]
      #v[.value 0x80, .value 0x7F, .value 0xFF, .value 0] ==
    #v[.value 11, .value 2, .value 13, .value 4]

#guard
  pblendvb (#v[.value 1, .poison] : ⟦Ty.vec 2 8⟧) #v[.poison, .value 12] #v[.poison, .value 0x80] ==
    #v[.poison, .value 12]

-- the unselected operand may be poison without poisoning the lane
#guard
  pblendvb (#v[.value 1, .poison] : ⟦Ty.vec 2 8⟧) #v[.poison, .value 12]
      #v[.value 0, .value 0xC0] ==
    #v[.value 1, .value 12]

/-! ## `reduceOr` — every lane, poison if one is -/

#guard
  reduceOr (#v[.value 0x1, .value 0x10, .value 0x100, .value 0x1000] : ⟦Ty.vec 4 64⟧) ==
    PoisonOr.value 0x1111#64

#guard reduceOr (#v[.value 0, .value 0] : ⟦Ty.vec 2 64⟧) == PoisonOr.value 0#64

#guard reduceOr (#v[.value 5] : ⟦Ty.vec 1 8⟧) == PoisonOr.value 5#8

#guard (reduceOr (#v[.value 0xFF, .value 1, .poison, .value 0] : ⟦Ty.vec 4 8⟧)).isPoison

/-! ## `reduceAdd` — the wrapping sum, poison if one lane is -/

#guard
  reduceAdd (#v[.value 0x1, .value 0x10, .value 0x100, .value 0x1000] : ⟦Ty.vec 4 64⟧) ==
    PoisonOr.value 0x1111#64

#guard reduceAdd (#v[.value 0xFF, .value 2] : ⟦Ty.vec 2 8⟧) == PoisonOr.value 1#8

#guard reduceAdd (#v[.value 5] : ⟦Ty.vec 1 8⟧) == PoisonOr.value 5#8

#guard (reduceAdd (#v[.value 1, .poison, .value 2, .value 3] : ⟦Ty.vec 4 8⟧)).isPoison

/-! ## `abs` and `usubSat` -/

#guard abs false (.value 0xFB#8) == PoisonOr.value 5#8

#guard abs false (.value 0x80#8) == PoisonOr.value 0x80#8

#guard (abs true (.value 0x80#8)).isPoison

#guard abs true (.value 7#8) == PoisonOr.value 7#8

#guard usubSat (.value 7#8) (.value 9#8) == PoisonOr.value 0#8

#guard usubSat (.value 9#8) (.value 7#8) == PoisonOr.value 2#8

/-! ## `subborrow` — `(borrow out, a - b - borrow in)`; any nonzero `c` borrows -/

private abbrev Sbb :=
  PoisonOr (BitVec 8) × PoisonOr (BitVec 64)

#guard (subborrow (.value 0) (.value 5#64) (.value 3#64) : Sbb) == (.value 0, .value 2)

#guard (subborrow (.value 1) (.value 5#64) (.value 3#64) : Sbb) == (.value 0, .value 1)

#guard (subborrow (.value 0x80) (.value 5#64) (.value 3#64) : Sbb) == (.value 0, .value 1)

#guard (subborrow (.value 0) (.value 3#64) (.value 5#64) : Sbb) == (.value 1, .value (-2))

-- `a = b`: a borrow in borrows out
#guard (subborrow (.value 0) (.value 5#64) (.value 5#64) : Sbb) == (.value 0, .value 0)

#guard (subborrow (.value 1) (.value 5#64) (.value 5#64) : Sbb) == (.value 1, .value (-1))

-- `b + 1` overflows 64 bits
#guard (subborrow (.value 1) (.value 0#64) (.value (-1 : BitVec 64)) : Sbb) == (.value 1, .value 0)

#guard
  (subborrow (.value 1) (.value (-1 : BitVec 64)) (.value (-1 : BitVec 64)) : Sbb) ==
    (.value 1, .value (-1))

#guard (subborrow .poison (.value 5#64) (.value 3#64) : Sbb) == (.poison, .poison)

#guard (subborrow (.value 0) (.value 5#64) .poison : Sbb) == (.poison, .poison)

/-! ## `uadd/usub.with.overflow` — the wrapped result and the carry or borrow out -/

private abbrev Ovf :=
  PoisonOr (BitVec 64) × PoisonOr (BitVec 1)

#guard (uaddWithOverflow (.value 5#64) (.value 3#64) : Ovf) == (.value 8, .value 0)

#guard (uaddWithOverflow (.value (-1 : BitVec 64)) (.value 1#64) : Ovf) == (.value 0, .value 1)

#guard
  (uaddWithOverflow (.value (-1 : BitVec 64)) (.value (-1 : BitVec 64)) : Ovf) ==
    (.value (-2), .value 1)

#guard (uaddWithOverflow .poison (.value 1#64) : Ovf) == (.poison, .poison)

#guard (usubWithOverflow (.value 5#64) (.value 3#64) : Ovf) == (.value 2, .value 0)

#guard (usubWithOverflow (.value 5#64) (.value 5#64) : Ovf) == (.value 0, .value 0)

#guard (usubWithOverflow (.value 3#64) (.value 5#64) : Ovf) == (.value (-2), .value 1)

#guard (usubWithOverflow (.value 3#64) .poison : Ovf) == (.poison, .poison)

/-! ## `ctpop` — the number of set bits -/

#guard ctpop (.value 0#64) == PoisonOr.value 0#64

#guard ctpop (.value 0b1011#64) == PoisonOr.value 3#64

#guard ctpop (.value (-1 : BitVec 64)) == PoisonOr.value 64#64

#guard ctpop (.value (-1 : BitVec 8)) == PoisonOr.value 8#8

#guard (ctpop .poison : PoisonOr (BitVec 64)) == .poison

/-! ## `extractvalue` — the member at a position, through arrays and structs -/

#guard
  (extractvalue [0] (.struct [.bv 8, .bv 64]) (.bv 8) rfl (.value 1, .value 2) : IntW 8) ==
    PoisonOr.value 1

#guard
  (extractvalue [1] (.struct [.bv 8, .bv 64]) (.bv 64) rfl (.value 1, .poison) : IntW 64).isPoison

#guard
  (extractvalue [1, 2] (.struct [.bv 8, .array 3 (.bv 16)]) (.bv 16) rfl
        (.value 1, #v[.value 4, .value 5, .value 6]) :
      IntW 16) ==
    PoisonOr.value 6

#guard
  (extractvalue [2, 1] (.array 3 (.struct [.bv 8, .bv 16, .bv 32])) (.bv 16) rfl
        #v[(.value 0, .value 0, .value 0), (.value 0, .value 0, .value 0),
          (.value 7, .value 8, .value 9)] :
      IntW 16) ==
    PoisonOr.value 8

-- a whole member
#guard
  (extractvalue [1] (.struct [.bv 8, .struct [.bv 8, .bv 8]]) (.struct [.bv 8, .bv 8]) rfl
        (.value 1, .value 2, .value 3) :
      PoisonOr (BitVec 8) × PoisonOr (BitVec 8)) ==
    (.value 2, .value 3)

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

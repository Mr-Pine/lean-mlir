module

import MLIR.Semantics.Effectful.Memory.Bits
meta import MLIR.Semantics.Effectful.Memory.Bits

/-! # `spliceBits`: evaluation -/

namespace MLIR.Tests

open MLIR.Memory

-- overwrite the low byte, leave the rest
#guard spliceBits 0xffffffff#32 0 0x00#8 == 0xffffff00#32

-- overwrite byte 1
#guard spliceBits 0xffffffff#32 8 0x00#8 == 0xffff00ff#32

-- overwrite the top byte
#guard spliceBits 0x00000000#32 24 0xab#8 == 0xab000000#32

-- a full-width splice replaces everything
#guard spliceBits 0xdeadbeef#32 0 0x12345678#32 == 0x12345678#32

-- writing past the end truncates rather than growing
#guard spliceBits 0x0000#16 8 0xabcd#16 == 0xcd00#16

-- a zero-width splice changes nothing
#guard spliceBits 0xdead#16 4 (0#0) == 0xdead#16

-- read back what was written, and the bits around it
#guard (spliceBits 0x00000000#32 8 0xab#8).extractLsb' 8 8 == 0xab#8

#guard (spliceBits 0xffffffff#32 8 0x00#8).extractLsb' 0 8 == 0xff#8

#guard (spliceBits 0xffffffff#32 8 0x00#8).extractLsb' 16 8 == 0xff#8

-- a sub-range of the written value
#guard (spliceBits 0x00000000#32 0 0x1234#16).extractLsb' 8 8 == 0x12#8

-- two splices at the same place: the second wins
#guard spliceBits (spliceBits 0#16 0 0xaa#8) 0 0xbb#8 == spliceBits 0#16 0 0xbb#8

-- disjoint splices commute
#guard
  spliceBits (spliceBits 0#16 0 0xaa#8) 8 0xbb#8 == spliceBits (spliceBits 0#16 8 0xbb#8) 0 0xaa#8

end MLIR.Tests

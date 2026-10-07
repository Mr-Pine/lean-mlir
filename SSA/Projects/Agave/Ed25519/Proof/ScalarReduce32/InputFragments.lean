import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.InputWords

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

theorem unpackV111_fragment (s : GlobalState) (a : Pointer) (bytes : BitVec 256)
    (hlive : SmallRange s.mem a 32) (hread : s.mem.readAt a 256 = bytes) :
    unpackV111 s a = inputFragment bytes 0 56 0 := by
  unfold unpackV111
  have h0_32 := MemoryState.readAt_add_of_readAt (off := 0#64)
    hlive.fits (hlive.no_wrap (k := 0) (by decide)) (w := 32) (by decide) hread
  simp only [Pointer.add_zero] at h0_32
  have h4_8 := MemoryState.readAt_add_of_readAt (off := 4#64)
    hlive.fits (hlive.no_wrap (k := 4) (by decide)) (w := 8) (by decide) hread
  have h5_8 := MemoryState.readAt_add_of_readAt (off := 5#64)
    hlive.fits (hlive.no_wrap (k := 5) (by decide)) (w := 8) (by decide) hread
  have h6_8 := MemoryState.readAt_add_of_readAt (off := 6#64)
    hlive.fits (hlive.no_wrap (k := 6) (by decide)) (w := 8) (by decide) hread
  have h7_8 := MemoryState.readAt_add_of_readAt (off := 7#64)
    hlive.fits (hlive.no_wrap (k := 7) (by decide)) (w := 8) (by decide) hread
  simp only [h0_32, h4_8, h5_8, h6_8, h7_8]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem unpackV116_fragment (s : GlobalState) (a : Pointer) (bytes : BitVec 256)
    (hlive : SmallRange s.mem a 32) (hread : s.mem.readAt a 256 = bytes) :
    unpackV116 s a = inputFragment bytes 0 64 0 := by
  unfold unpackV116
  have h0_32 := MemoryState.readAt_add_of_readAt (off := 0#64)
    hlive.fits (hlive.no_wrap (k := 0) (by decide)) (w := 32) (by decide) hread
  simp only [Pointer.add_zero] at h0_32
  have h4_8 := MemoryState.readAt_add_of_readAt (off := 4#64)
    hlive.fits (hlive.no_wrap (k := 4) (by decide)) (w := 8) (by decide) hread
  have h5_8 := MemoryState.readAt_add_of_readAt (off := 5#64)
    hlive.fits (hlive.no_wrap (k := 5) (by decide)) (w := 8) (by decide) hread
  have h6_8 := MemoryState.readAt_add_of_readAt (off := 6#64)
    hlive.fits (hlive.no_wrap (k := 6) (by decide)) (w := 8) (by decide) hread
  have h7_8 := MemoryState.readAt_add_of_readAt (off := 7#64)
    hlive.fits (hlive.no_wrap (k := 7) (by decide)) (w := 8) (by decide) hread
  simp only [h0_32, h4_8, h5_8, h6_8, h7_8]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem unpackV124_fragment (s : GlobalState) (a : Pointer) (bytes : BitVec 256)
    (hlive : SmallRange s.mem a 32) (hread : s.mem.readAt a 256 = bytes) :
    unpackV124 s a = inputFragment bytes 64 40 0 := by
  unfold unpackV124
  have h8_32 := MemoryState.readAt_add_of_readAt (off := 8#64)
    hlive.fits (hlive.no_wrap (k := 8) (by decide)) (w := 32) (by decide) hread
  have h12_8 := MemoryState.readAt_add_of_readAt (off := 12#64)
    hlive.fits (hlive.no_wrap (k := 12) (by decide)) (w := 8) (by decide) hread
  have h13_8 := MemoryState.readAt_add_of_readAt (off := 13#64)
    hlive.fits (hlive.no_wrap (k := 13) (by decide)) (w := 8) (by decide) hread
  have h14_16 := MemoryState.readAt_add_of_readAt (off := 14#64)
    hlive.fits (hlive.no_wrap (k := 14) (by decide)) (w := 16) (by decide) hread
  simp only [h8_32, h12_8, h13_8, h14_16]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem unpackV133_fragment (s : GlobalState) (a : Pointer) (bytes : BitVec 256)
    (hlive : SmallRange s.mem a 32) (hread : s.mem.readAt a 256 = bytes) :
    unpackV133 s a = inputFragment bytes 104 24 40 := by
  unfold unpackV133
  have h8_32 := MemoryState.readAt_add_of_readAt (off := 8#64)
    hlive.fits (hlive.no_wrap (k := 8) (by decide)) (w := 32) (by decide) hread
  have h12_8 := MemoryState.readAt_add_of_readAt (off := 12#64)
    hlive.fits (hlive.no_wrap (k := 12) (by decide)) (w := 8) (by decide) hread
  have h13_8 := MemoryState.readAt_add_of_readAt (off := 13#64)
    hlive.fits (hlive.no_wrap (k := 13) (by decide)) (w := 8) (by decide) hread
  have h14_16 := MemoryState.readAt_add_of_readAt (off := 14#64)
    hlive.fits (hlive.no_wrap (k := 14) (by decide)) (w := 16) (by decide) hread
  simp only [h8_32, h12_8, h13_8, h14_16]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem unpackV134_fragment (s : GlobalState) (a : Pointer) (bytes : BitVec 256)
    (hlive : SmallRange s.mem a 32) (hread : s.mem.readAt a 256 = bytes) :
    unpackV134 s a = inputFragment bytes 64 64 0 := by
  unfold unpackV134
  have h8_32 := MemoryState.readAt_add_of_readAt (off := 8#64)
    hlive.fits (hlive.no_wrap (k := 8) (by decide)) (w := 32) (by decide) hread
  have h12_8 := MemoryState.readAt_add_of_readAt (off := 12#64)
    hlive.fits (hlive.no_wrap (k := 12) (by decide)) (w := 8) (by decide) hread
  have h13_8 := MemoryState.readAt_add_of_readAt (off := 13#64)
    hlive.fits (hlive.no_wrap (k := 13) (by decide)) (w := 8) (by decide) hread
  have h14_16 := MemoryState.readAt_add_of_readAt (off := 14#64)
    hlive.fits (hlive.no_wrap (k := 14) (by decide)) (w := 16) (by decide) hread
  simp only [h8_32, h12_8, h13_8, h14_16]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem unpackV147_fragment (s : GlobalState) (a : Pointer) (bytes : BitVec 256)
    (hlive : SmallRange s.mem a 32) (hread : s.mem.readAt a 256 = bytes) :
    unpackV147 s a = inputFragment bytes 128 32 0 := by
  unfold unpackV147
  have h16_16 := MemoryState.readAt_add_of_readAt (off := 16#64)
    hlive.fits (hlive.no_wrap (k := 16) (by decide)) (w := 16) (by decide) hread
  have h18_8 := MemoryState.readAt_add_of_readAt (off := 18#64)
    hlive.fits (hlive.no_wrap (k := 18) (by decide)) (w := 8) (by decide) hread
  have h19_8 := MemoryState.readAt_add_of_readAt (off := 19#64)
    hlive.fits (hlive.no_wrap (k := 19) (by decide)) (w := 8) (by decide) hread
  have h20_32 := MemoryState.readAt_add_of_readAt (off := 20#64)
    hlive.fits (hlive.no_wrap (k := 20) (by decide)) (w := 32) (by decide) hread
  simp only [h16_16, h18_8, h19_8, h20_32]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem unpackV152_fragment (s : GlobalState) (a : Pointer) (bytes : BitVec 256)
    (hlive : SmallRange s.mem a 32) (hread : s.mem.readAt a 256 = bytes) :
    unpackV152 s a = inputFragment bytes 128 64 0 := by
  unfold unpackV152
  have h16_16 := MemoryState.readAt_add_of_readAt (off := 16#64)
    hlive.fits (hlive.no_wrap (k := 16) (by decide)) (w := 16) (by decide) hread
  have h18_8 := MemoryState.readAt_add_of_readAt (off := 18#64)
    hlive.fits (hlive.no_wrap (k := 18) (by decide)) (w := 8) (by decide) hread
  have h19_8 := MemoryState.readAt_add_of_readAt (off := 19#64)
    hlive.fits (hlive.no_wrap (k := 19) (by decide)) (w := 8) (by decide) hread
  have h20_32 := MemoryState.readAt_add_of_readAt (off := 20#64)
    hlive.fits (hlive.no_wrap (k := 20) (by decide)) (w := 32) (by decide) hread
  simp only [h16_16, h18_8, h19_8, h20_32]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem unpackV160_fragment (s : GlobalState) (a : Pointer) (bytes : BitVec 256)
    (hlive : SmallRange s.mem a 32) (hread : s.mem.readAt a 256 = bytes) :
    unpackV160 s a = inputFragment bytes 192 16 0 := by
  unfold unpackV160
  have h24_8 := MemoryState.readAt_add_of_readAt (off := 24#64)
    hlive.fits (hlive.no_wrap (k := 24) (by decide)) (w := 8) (by decide) hread
  have h25_8 := MemoryState.readAt_add_of_readAt (off := 25#64)
    hlive.fits (hlive.no_wrap (k := 25) (by decide)) (w := 8) (by decide) hread
  have h26_32 := MemoryState.readAt_add_of_readAt (off := 26#64)
    hlive.fits (hlive.no_wrap (k := 26) (by decide)) (w := 32) (by decide) hread
  have h30_16 := MemoryState.readAt_add_of_readAt (off := 30#64)
    hlive.fits (hlive.no_wrap (k := 30) (by decide)) (w := 16) (by decide) hread
  simp only [h24_8, h25_8, h26_32, h30_16]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem unpackV169_fragment (s : GlobalState) (a : Pointer) (bytes : BitVec 256)
    (hlive : SmallRange s.mem a 32) (hread : s.mem.readAt a 256 = bytes) :
    unpackV169 s a = inputFragment bytes 208 48 16 := by
  unfold unpackV169
  have h24_8 := MemoryState.readAt_add_of_readAt (off := 24#64)
    hlive.fits (hlive.no_wrap (k := 24) (by decide)) (w := 8) (by decide) hread
  have h25_8 := MemoryState.readAt_add_of_readAt (off := 25#64)
    hlive.fits (hlive.no_wrap (k := 25) (by decide)) (w := 8) (by decide) hread
  have h26_32 := MemoryState.readAt_add_of_readAt (off := 26#64)
    hlive.fits (hlive.no_wrap (k := 26) (by decide)) (w := 32) (by decide) hread
  have h30_16 := MemoryState.readAt_add_of_readAt (off := 30#64)
    hlive.fits (hlive.no_wrap (k := 30) (by decide)) (w := 16) (by decide) hread
  simp only [h24_8, h25_8, h26_32, h30_16]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem unpackV170_fragment (s : GlobalState) (a : Pointer) (bytes : BitVec 256)
    (hlive : SmallRange s.mem a 32) (hread : s.mem.readAt a 256 = bytes) :
    unpackV170 s a = inputFragment bytes 192 64 0 := by
  unfold unpackV170
  have h24_8 := MemoryState.readAt_add_of_readAt (off := 24#64)
    hlive.fits (hlive.no_wrap (k := 24) (by decide)) (w := 8) (by decide) hread
  have h25_8 := MemoryState.readAt_add_of_readAt (off := 25#64)
    hlive.fits (hlive.no_wrap (k := 25) (by decide)) (w := 8) (by decide) hread
  have h26_32 := MemoryState.readAt_add_of_readAt (off := 26#64)
    hlive.fits (hlive.no_wrap (k := 26) (by decide)) (w := 32) (by decide) hread
  have h30_16 := MemoryState.readAt_add_of_readAt (off := 30#64)
    hlive.fits (hlive.no_wrap (k := 30) (by decide)) (w := 16) (by decide) hread
  simp only [h24_8, h25_8, h26_32, h30_16]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

end Agave.Ed25519.ScalarReduce32.Execution

import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputChunk0
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputChunk1
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputChunk2
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputChunk3
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputChunk4
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputChunk5
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputChunk6
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputChunk7
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputSplitWords

/-! Register-level connection from mixed-width memory reads to slices of the
original 512-bit input. Each endpoint covers one source fragment consumed by
the ten split stores, independently of unrelated scratch memory. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 100000

theorem inputFragment_reg105 (E : Env program.Γ) (mem : MemoryState)
    (input : Pointer) (bytes : BitVec 512)
    (hlive : SmallRange mem input 64) (hread : mem.readAt input 512 = bytes) :
    (inputChunk0Env E mem input).read (%105) =
      .value (inputFragment bytes 0 56 0) := by
  simp [inputChunk0Env, mlir_env]
  have hr89 := MemoryState.readAt_add_of_readAt (off := 0#64)
    hlive.fits (hlive.no_wrap (k := 0) (by decide)) (w := 32) (by decide) hread
  simp only [Pointer.add_zero] at hr89
  have hr92 := MemoryState.readAt_add_of_readAt (off := 4#64)
    hlive.fits (hlive.no_wrap (k := 4) (by decide)) (w := 8) (by decide) hread
  have hr97 := MemoryState.readAt_add_of_readAt (off := 5#64)
    hlive.fits (hlive.no_wrap (k := 5) (by decide)) (w := 8) (by decide) hread
  have hr102 := MemoryState.readAt_add_of_readAt (off := 6#64)
    hlive.fits (hlive.no_wrap (k := 6) (by decide)) (w := 8) (by decide) hread
  rw [hr89, hr92, hr97, hr102]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem inputFragment_reg110 (E : Env program.Γ) (mem : MemoryState)
    (input : Pointer) (bytes : BitVec 512)
    (hlive : SmallRange mem input 64) (hread : mem.readAt input 512 = bytes) :
    (inputChunk0Env E mem input).read (%110) =
      .value (inputFragment bytes 0 64 0) := by
  simp [inputChunk0Env, mlir_env]
  have hr89 := MemoryState.readAt_add_of_readAt (off := 0#64)
    hlive.fits (hlive.no_wrap (k := 0) (by decide)) (w := 32) (by decide) hread
  simp only [Pointer.add_zero] at hr89
  have hr92 := MemoryState.readAt_add_of_readAt (off := 4#64)
    hlive.fits (hlive.no_wrap (k := 4) (by decide)) (w := 8) (by decide) hread
  have hr97 := MemoryState.readAt_add_of_readAt (off := 5#64)
    hlive.fits (hlive.no_wrap (k := 5) (by decide)) (w := 8) (by decide) hread
  have hr102 := MemoryState.readAt_add_of_readAt (off := 6#64)
    hlive.fits (hlive.no_wrap (k := 6) (by decide)) (w := 8) (by decide) hread
  have hr107 := MemoryState.readAt_add_of_readAt (off := 7#64)
    hlive.fits (hlive.no_wrap (k := 7) (by decide)) (w := 8) (by decide) hread
  rw [hr89, hr92, hr97, hr102, hr107]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem inputFragment_reg118 (E : Env program.Γ) (mem : MemoryState)
    (input : Pointer) (bytes : BitVec 512)
    (hlive : SmallRange mem input 64) (hread : mem.readAt input 512 = bytes) :
    (inputChunk1Env E mem input).read (%118) =
      .value (inputFragment bytes 64 40 0) := by
  simp [inputChunk1Env, mlir_env]
  have hr112 := MemoryState.readAt_add_of_readAt (off := 8#64)
    hlive.fits (hlive.no_wrap (k := 8) (by decide)) (w := 32) (by decide) hread
  have hr115 := MemoryState.readAt_add_of_readAt (off := 12#64)
    hlive.fits (hlive.no_wrap (k := 12) (by decide)) (w := 8) (by decide) hread
  rw [hr112, hr115]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem inputFragment_reg127 (E : Env program.Γ) (mem : MemoryState)
    (input : Pointer) (bytes : BitVec 512)
    (hlive : SmallRange mem input 64) (hread : mem.readAt input 512 = bytes) :
    (inputChunk1Env E mem input).read (%127) =
      .value (inputFragment bytes 104 24 40) := by
  simp [inputChunk1Env, mlir_env]
  have hr120 := MemoryState.readAt_add_of_readAt (off := 13#64)
    hlive.fits (hlive.no_wrap (k := 13) (by decide)) (w := 8) (by decide) hread
  have hr124 := MemoryState.readAt_add_of_readAt (off := 14#64)
    hlive.fits (hlive.no_wrap (k := 14) (by decide)) (w := 16) (by decide) hread
  rw [hr120, hr124]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem inputFragment_reg141 (E : Env program.Γ) (mem : MemoryState)
    (input : Pointer) (bytes : BitVec 512)
    (hlive : SmallRange mem input 64) (hread : mem.readAt input 512 = bytes) :
    (inputChunk2Env E mem input).read (%141) =
      .value (inputFragment bytes 128 32 0) := by
  simp [inputChunk2Env, mlir_env]
  have hr130 := MemoryState.readAt_add_of_readAt (off := 16#64)
    hlive.fits (hlive.no_wrap (k := 16) (by decide)) (w := 16) (by decide) hread
  have hr133 := MemoryState.readAt_add_of_readAt (off := 18#64)
    hlive.fits (hlive.no_wrap (k := 18) (by decide)) (w := 8) (by decide) hread
  have hr138 := MemoryState.readAt_add_of_readAt (off := 19#64)
    hlive.fits (hlive.no_wrap (k := 19) (by decide)) (w := 8) (by decide) hread
  rw [hr130, hr133, hr138]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem inputFragment_reg151 (E : Env program.Γ) (mem : MemoryState)
    (input : Pointer) (bytes : BitVec 512)
    (hlive : SmallRange mem input 64) (hread : mem.readAt input 512 = bytes) :
    (inputChunk2Env E mem input).read (%151) =
      .value (inputFragment bytes 128 64 0) := by
  simp [inputChunk2Env, mlir_env]
  have hr130 := MemoryState.readAt_add_of_readAt (off := 16#64)
    hlive.fits (hlive.no_wrap (k := 16) (by decide)) (w := 16) (by decide) hread
  have hr133 := MemoryState.readAt_add_of_readAt (off := 18#64)
    hlive.fits (hlive.no_wrap (k := 18) (by decide)) (w := 8) (by decide) hread
  have hr138 := MemoryState.readAt_add_of_readAt (off := 19#64)
    hlive.fits (hlive.no_wrap (k := 19) (by decide)) (w := 8) (by decide) hread
  have hr143 := MemoryState.readAt_add_of_readAt (off := 20#64)
    hlive.fits (hlive.no_wrap (k := 20) (by decide)) (w := 16) (by decide) hread
  have hr147 := MemoryState.readAt_add_of_readAt (off := 22#64)
    hlive.fits (hlive.no_wrap (k := 22) (by decide)) (w := 16) (by decide) hread
  rw [hr130, hr133, hr138, hr143, hr147]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem inputFragment_reg159 (E : Env program.Γ) (mem : MemoryState)
    (input : Pointer) (bytes : BitVec 512)
    (hlive : SmallRange mem input 64) (hread : mem.readAt input 512 = bytes) :
    (inputChunk3Env E mem input).read (%159) =
      .value (inputFragment bytes 192 16 0) := by
  simp [inputChunk3Env, mlir_env]
  have hr153 := MemoryState.readAt_add_of_readAt (off := 24#64)
    hlive.fits (hlive.no_wrap (k := 24) (by decide)) (w := 8) (by decide) hread
  have hr156 := MemoryState.readAt_add_of_readAt (off := 25#64)
    hlive.fits (hlive.no_wrap (k := 25) (by decide)) (w := 8) (by decide) hread
  rw [hr153, hr156]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem inputFragment_reg173 (E : Env program.Γ) (mem : MemoryState)
    (input : Pointer) (bytes : BitVec 512)
    (hlive : SmallRange mem input 64) (hread : mem.readAt input 512 = bytes) :
    (inputChunk3Env E mem input).read (%173) =
      .value (inputFragment bytes 208 48 16) := by
  simp [inputChunk3Env, mlir_env]
  have hr161 := MemoryState.readAt_add_of_readAt (off := 26#64)
    hlive.fits (hlive.no_wrap (k := 26) (by decide)) (w := 16) (by decide) hread
  have hr165 := MemoryState.readAt_add_of_readAt (off := 28#64)
    hlive.fits (hlive.no_wrap (k := 28) (by decide)) (w := 16) (by decide) hread
  have hr170 := MemoryState.readAt_add_of_readAt (off := 30#64)
    hlive.fits (hlive.no_wrap (k := 30) (by decide)) (w := 16) (by decide) hread
  rw [hr161, hr165, hr170]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem inputFragment_reg177 (E : Env program.Γ) (mem : MemoryState)
    (input : Pointer) (bytes : BitVec 512)
    (hlive : SmallRange mem input 64) (hread : mem.readAt input 512 = bytes) :
    (inputChunk4Env E mem input).read (%177) =
      .value (inputFragment bytes 256 8 0) := by
  simp [inputChunk4Env, mlir_env]
  have hr176 := MemoryState.readAt_add_of_readAt (off := 32#64)
    hlive.fits (hlive.no_wrap (k := 32) (by decide)) (w := 8) (by decide) hread
  rw [hr176]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem inputFragment_reg195 (E : Env program.Γ) (mem : MemoryState)
    (input : Pointer) (bytes : BitVec 512)
    (hlive : SmallRange mem input 64) (hread : mem.readAt input 512 = bytes) :
    (inputChunk4Env E mem input).read (%195) =
      .value (inputFragment bytes 304 16 48) := by
  simp [inputChunk4Env, mlir_env]
  have hr193 := MemoryState.readAt_add_of_readAt (off := 38#64)
    hlive.fits (hlive.no_wrap (k := 38) (by decide)) (w := 16) (by decide) hread
  rw [hr193]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem inputFragment_reg197 (E : Env program.Γ) (mem : MemoryState)
    (input : Pointer) (bytes : BitVec 512)
    (hlive : SmallRange mem input 64) (hread : mem.readAt input 512 = bytes) :
    (inputChunk4Env E mem input).read (%197) =
      .value (inputFragment bytes 256 64 0) := by
  simp [inputChunk4Env, mlir_env]
  have hr176 := MemoryState.readAt_add_of_readAt (off := 32#64)
    hlive.fits (hlive.no_wrap (k := 32) (by decide)) (w := 8) (by decide) hread
  have hr179 := MemoryState.readAt_add_of_readAt (off := 33#64)
    hlive.fits (hlive.no_wrap (k := 33) (by decide)) (w := 8) (by decide) hread
  have hr183 := MemoryState.readAt_add_of_readAt (off := 34#64)
    hlive.fits (hlive.no_wrap (k := 34) (by decide)) (w := 16) (by decide) hread
  have hr188 := MemoryState.readAt_add_of_readAt (off := 36#64)
    hlive.fits (hlive.no_wrap (k := 36) (by decide)) (w := 16) (by decide) hread
  have hr193 := MemoryState.readAt_add_of_readAt (off := 38#64)
    hlive.fits (hlive.no_wrap (k := 38) (by decide)) (w := 16) (by decide) hread
  rw [hr176, hr179, hr183, hr188, hr193]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem inputFragment_reg210 (E : Env program.Γ) (mem : MemoryState)
    (input : Pointer) (bytes : BitVec 512)
    (hlive : SmallRange mem input 64) (hread : mem.readAt input 512 = bytes) :
    (inputChunk5Env E mem input).read (%210) =
      .value (inputFragment bytes 320 48 0) := by
  simp [inputChunk5Env, mlir_env]
  have hr199 := MemoryState.readAt_add_of_readAt (off := 40#64)
    hlive.fits (hlive.no_wrap (k := 40) (by decide)) (w := 32) (by decide) hread
  have hr202 := MemoryState.readAt_add_of_readAt (off := 44#64)
    hlive.fits (hlive.no_wrap (k := 44) (by decide)) (w := 8) (by decide) hread
  have hr207 := MemoryState.readAt_add_of_readAt (off := 45#64)
    hlive.fits (hlive.no_wrap (k := 45) (by decide)) (w := 8) (by decide) hread
  rw [hr199, hr202, hr207]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem inputFragment_reg215 (E : Env program.Γ) (mem : MemoryState)
    (input : Pointer) (bytes : BitVec 512)
    (hlive : SmallRange mem input 64) (hread : mem.readAt input 512 = bytes) :
    (inputChunk5Env E mem input).read (%215) =
      .value (inputFragment bytes 320 64 0) := by
  simp [inputChunk5Env, mlir_env]
  have hr199 := MemoryState.readAt_add_of_readAt (off := 40#64)
    hlive.fits (hlive.no_wrap (k := 40) (by decide)) (w := 32) (by decide) hread
  have hr202 := MemoryState.readAt_add_of_readAt (off := 44#64)
    hlive.fits (hlive.no_wrap (k := 44) (by decide)) (w := 8) (by decide) hread
  have hr207 := MemoryState.readAt_add_of_readAt (off := 45#64)
    hlive.fits (hlive.no_wrap (k := 45) (by decide)) (w := 8) (by decide) hread
  have hr212 := MemoryState.readAt_add_of_readAt (off := 46#64)
    hlive.fits (hlive.no_wrap (k := 46) (by decide)) (w := 16) (by decide) hread
  rw [hr199, hr202, hr207, hr212]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem inputFragment_reg228 (E : Env program.Γ) (mem : MemoryState)
    (input : Pointer) (bytes : BitVec 512)
    (hlive : SmallRange mem input 64) (hread : mem.readAt input 512 = bytes) :
    (inputChunk6Env E mem input).read (%228) =
      .value (inputFragment bytes 384 32 0) := by
  simp [inputChunk6Env, mlir_env]
  have hr217 := MemoryState.readAt_add_of_readAt (off := 48#64)
    hlive.fits (hlive.no_wrap (k := 48) (by decide)) (w := 16) (by decide) hread
  have hr220 := MemoryState.readAt_add_of_readAt (off := 50#64)
    hlive.fits (hlive.no_wrap (k := 50) (by decide)) (w := 8) (by decide) hread
  have hr225 := MemoryState.readAt_add_of_readAt (off := 51#64)
    hlive.fits (hlive.no_wrap (k := 51) (by decide)) (w := 8) (by decide) hread
  rw [hr217, hr220, hr225]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem inputFragment_reg237 (E : Env program.Γ) (mem : MemoryState)
    (input : Pointer) (bytes : BitVec 512)
    (hlive : SmallRange mem input 64) (hread : mem.readAt input 512 = bytes) :
    (inputChunk6Env E mem input).read (%237) =
      .value (inputFragment bytes 416 32 32) := by
  simp [inputChunk6Env, mlir_env]
  have hr230 := MemoryState.readAt_add_of_readAt (off := 52#64)
    hlive.fits (hlive.no_wrap (k := 52) (by decide)) (w := 16) (by decide) hread
  have hr234 := MemoryState.readAt_add_of_readAt (off := 54#64)
    hlive.fits (hlive.no_wrap (k := 54) (by decide)) (w := 16) (by decide) hread
  rw [hr230, hr234]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem inputFragment_reg246 (E : Env program.Γ) (mem : MemoryState)
    (input : Pointer) (bytes : BitVec 512)
    (hlive : SmallRange mem input 64) (hread : mem.readAt input 512 = bytes) :
    (inputChunk7Env E mem input).read (%246) =
      .value (inputFragment bytes 448 24 0) := by
  simp [inputChunk7Env, mlir_env]
  have hr240 := MemoryState.readAt_add_of_readAt (off := 56#64)
    hlive.fits (hlive.no_wrap (k := 56) (by decide)) (w := 16) (by decide) hread
  have hr243 := MemoryState.readAt_add_of_readAt (off := 58#64)
    hlive.fits (hlive.no_wrap (k := 58) (by decide)) (w := 8) (by decide) hread
  rw [hr240, hr243]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

theorem inputFragment_reg261 (E : Env program.Γ) (mem : MemoryState)
    (input : Pointer) (bytes : BitVec 512)
    (hlive : SmallRange mem input 64) (hread : mem.readAt input 512 = bytes) :
    (inputChunk7Env E mem input).read (%261) =
      .value (inputFragment bytes 448 64 0) := by
  simp [inputChunk7Env, mlir_env]
  have hr240 := MemoryState.readAt_add_of_readAt (off := 56#64)
    hlive.fits (hlive.no_wrap (k := 56) (by decide)) (w := 16) (by decide) hread
  have hr243 := MemoryState.readAt_add_of_readAt (off := 58#64)
    hlive.fits (hlive.no_wrap (k := 58) (by decide)) (w := 8) (by decide) hread
  have hr248 := MemoryState.readAt_add_of_readAt (off := 59#64)
    hlive.fits (hlive.no_wrap (k := 59) (by decide)) (w := 8) (by decide) hread
  have hr252 := MemoryState.readAt_add_of_readAt (off := 60#64)
    hlive.fits (hlive.no_wrap (k := 60) (by decide)) (w := 16) (by decide) hread
  have hr257 := MemoryState.readAt_add_of_readAt (off := 62#64)
    hlive.fits (hlive.no_wrap (k := 62) (by decide)) (w := 16) (by decide) hread
  rw [hr240, hr243, hr248, hr252, hr257]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [inputFragment, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  grind only [BitVec.getLsbD_of_ge]

end Agave.Ed25519.Verifier.Execution.ScalarWide

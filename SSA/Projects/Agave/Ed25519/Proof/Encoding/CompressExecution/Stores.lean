import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Program
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Step
import Mathlib.Tactic.IntervalCases

/-! Exact output-store suffix of the imported compressor. The entry, inversion,
and canonicalization instructions precede this suffix and have separate obligations. -/
namespace Agave.Ed25519.Encoding.Compress.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

abbrev Bytes := Fin 32 → BitVec 8

/-- Concrete memory after the emitted 32 stores, in source order. -/
def storeBytes (m : MemoryState) (out : Pointer) (bytes : Bytes) : MemoryState :=
  (((((((((((((((((((((((((((((((m.storeAt out (bytes 0)).storeAt (out.add 1) (bytes 1)).storeAt (out.add 2) (bytes 2)).storeAt (out.add 3) (bytes 3)).storeAt (out.add 4) (bytes 4)).storeAt (out.add 5) (bytes 5)).storeAt (out.add 6) (bytes 6)).storeAt (out.add 7) (bytes 7)).storeAt (out.add 8) (bytes 8)).storeAt (out.add 9) (bytes 9)).storeAt (out.add 10) (bytes 10)).storeAt (out.add 11) (bytes 11)).storeAt (out.add 12) (bytes 12)).storeAt (out.add 13) (bytes 13)).storeAt (out.add 14) (bytes 14)).storeAt (out.add 15) (bytes 15)).storeAt (out.add 16) (bytes 16)).storeAt (out.add 17) (bytes 17)).storeAt (out.add 18) (bytes 18)).storeAt (out.add 19) (bytes 19)).storeAt (out.add 20) (bytes 20)).storeAt (out.add 21) (bytes 21)).storeAt (out.add 22) (bytes 22)).storeAt (out.add 23) (bytes 23)).storeAt (out.add 24) (bytes 24)).storeAt (out.add 25) (bytes 25)).storeAt (out.add 26) (bytes 26)).storeAt (out.add 27) (bytes 27)).storeAt (out.add 28) (bytes 28)).storeAt (out.add 29) (bytes 29)).storeAt (out.add 30) (bytes 30)).storeAt (out.add 31) (bytes 31)

def storeEnv (E : Env program.Γ) (bytes : Bytes) : Env program.Γ :=
  E[%31 := .value 1#64,
    %24 := .value 2#64,
    %16 := .value 3#64,
    %37 := .value 4#64,
    %17 := .value 5#64,
    %23 := .value 6#64,
    %15 := .value 7#64,
    %11 := .value 8#64,
    %45 := .value 9#64,
    %25 := .value 10#64,
    %46 := .value 11#64,
    %38 := .value 12#64,
    %18 := .value 13#64,
    %47 := .value 14#64,
    %32 := .value 15#64,
    %12 := .value 16#64,
    %48 := .value 17#64,
    %26 := .value 18#64,
    %10 := .value 19#64,
    %39 := .value 20#64,
    %19 := .value 21#64,
    %49 := .value 22#64,
    %33 := .value 23#64,
    %13 := .value 24#64,
    %50 := .value 25#64,
    %27 := .value 26#64,
    %51 := .value 27#64,
    %40 := .value 28#64,
    %20 := .value 29#64,
    %52 := .value 30#64,
    %34 := .value 31#64,
    %112 := .value (bytes 0),
    %114 := .value (bytes 1),
    %116 := .value (bytes 2),
    %118 := .value (bytes 3),
    %120 := .value (bytes 4),
    %122 := .value (bytes 5),
    %127 := .value (bytes 6),
    %129 := .value (bytes 7),
    %131 := .value (bytes 8),
    %133 := .value (bytes 9),
    %135 := .value (bytes 10),
    %137 := .value (bytes 11),
    %141 := .value (bytes 12),
    %143 := .value (bytes 13),
    %145 := .value (bytes 14),
    %147 := .value (bytes 15),
    %149 := .value (bytes 16),
    %151 := .value (bytes 17),
    %153 := .value (bytes 18),
    %157 := .value (bytes 19),
    %159 := .value (bytes 20),
    %161 := .value (bytes 21),
    %163 := .value (bytes 22),
    %165 := .value (bytes 23),
    %167 := .value (bytes 24),
    %171 := .value (bytes 25),
    %173 := .value (bytes 26),
    %175 := .value (bytes 27),
    %177 := .value (bytes 28),
    %179 := .value (bytes 29),
    %181 := .value (bytes 30),
    %224 := .value (bytes 31)]

theorem storeEnv_args (E : Env program.Γ) (bytes : Bytes) :
    (storeEnv E bytes).args = E.args := by
  simp only [storeEnv, Env.write_args]

/-- Slicing retains the original Γ, parameter map and return instruction. -/
abbrev storeProgram (p : Primitives) : Func :=
  { program p with blocks := fun _ =>
      { program.entry p with body := (program.entry p).body.drop 243 } }

theorem storeProgram_body (p : Primitives) :
    ((storeProgram p).blocks 0).body = (program.entry p).body.drop 243 := rfl

/-- Every emitted byte store executes from a live 32-byte destination. -/
theorem store_run (p : Primitives) (E : Env program.Γ) (out : Pointer) (bytes : Bytes)
    (s : GlobalState) (hr : SmallRange s.mem out 32)
    (hout : E.read (%arg0) = .value out) :
    (storeProgram p).runFrom (storeEnv E bytes) 0 s =
      .value (.nil, {s with mem := storeBytes s.mem out bytes}) := by
  have hr0 := hr.fits_add (k := 0) (count := 1) (by decide)
  have hr1 := hr.fits_add (k := 1) (count := 1) (by decide)
  have hr2 := hr.fits_add (k := 2) (count := 1) (by decide)
  have hr3 := hr.fits_add (k := 3) (count := 1) (by decide)
  have hr4 := hr.fits_add (k := 4) (count := 1) (by decide)
  have hr5 := hr.fits_add (k := 5) (count := 1) (by decide)
  have hr6 := hr.fits_add (k := 6) (count := 1) (by decide)
  have hr7 := hr.fits_add (k := 7) (count := 1) (by decide)
  have hr8 := hr.fits_add (k := 8) (count := 1) (by decide)
  have hr9 := hr.fits_add (k := 9) (count := 1) (by decide)
  have hr10 := hr.fits_add (k := 10) (count := 1) (by decide)
  have hr11 := hr.fits_add (k := 11) (count := 1) (by decide)
  have hr12 := hr.fits_add (k := 12) (count := 1) (by decide)
  have hr13 := hr.fits_add (k := 13) (count := 1) (by decide)
  have hr14 := hr.fits_add (k := 14) (count := 1) (by decide)
  have hr15 := hr.fits_add (k := 15) (count := 1) (by decide)
  have hr16 := hr.fits_add (k := 16) (count := 1) (by decide)
  have hr17 := hr.fits_add (k := 17) (count := 1) (by decide)
  have hr18 := hr.fits_add (k := 18) (count := 1) (by decide)
  have hr19 := hr.fits_add (k := 19) (count := 1) (by decide)
  have hr20 := hr.fits_add (k := 20) (count := 1) (by decide)
  have hr21 := hr.fits_add (k := 21) (count := 1) (by decide)
  have hr22 := hr.fits_add (k := 22) (count := 1) (by decide)
  have hr23 := hr.fits_add (k := 23) (count := 1) (by decide)
  have hr24 := hr.fits_add (k := 24) (count := 1) (by decide)
  have hr25 := hr.fits_add (k := 25) (count := 1) (by decide)
  have hr26 := hr.fits_add (k := 26) (count := 1) (by decide)
  have hr27 := hr.fits_add (k := 27) (count := 1) (by decide)
  have hr28 := hr.fits_add (k := 28) (count := 1) (by decide)
  have hr29 := hr.fits_add (k := 29) (count := 1) (by decide)
  have hr30 := hr.fits_add (k := 30) (count := 1) (by decide)
  have hr31 := hr.fits_add (k := 31) (count := 1) (by decide)
  simp only [Pointer.add_zero] at hr0
  change E.args 0 = .value out at hout
  generalize hE : storeEnv E bytes = E'
  symm at hE
  have hEargs : E'.args = E.args :=
    (congrArg Env.args hE).trans (storeEnv_args E bytes)
  dsimp only [storeEnv] at hE
  extract_state
  block_init
  step_store [hout]
  have hgep := hr.gep (k := 1) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 2) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 3) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 4) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 5) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 6) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 7) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 9) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 10) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 11) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 12) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 13) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 14) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 15) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 17) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 18) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 19) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 20) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 21) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 22) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 23) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 25) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 26) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 27) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 28) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 29) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 30) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 31) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  step_pure
  rw [BasicBlock.runBodyFrom_done (Nat.le_of_ble_eq_true rfl)]
  simp only [EffectM.pure_eq, PoisonOr.value_bind, reduceBlockExit,
    reduceFuncContinue, Exit.run, Regs.read_nil]
  rw [hS]
  rfl

/-- All 32 byte stores reconstruct the entire externally observed bit-vector. -/
theorem storeBytes_read (m : MemoryState) (out : Pointer) (bits : BitVec 256)
    (hr : SmallRange m out 32) :
    (storeBytes m out (fun i => bits.extractLsb' (8 * i.val) 8)).readAt out 256 = bits := by
  let m0 := m
  have hf0 : Fits m0 out 256 := hr.fits
  let m1 := m0.storeAt out (bits.extractLsb' 0 8)
  have hf1 : Fits m1 out 256 := hf0.storeAt
  have hread0 : m1.readAt out 256 = Memory.spliceBits (m0.readAt out 256) 0 (bits.extractLsb' 0 8) := by
    simpa only [m1, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 0#64) hf0 (hr.no_wrap (k := 0) (by decide))
        (by decide) (bits.extractLsb' 0 8))
  let m2 := m1.storeAt (out.add 1) (bits.extractLsb' 8 8)
  have hf2 : Fits m2 out 256 := hf1.storeAt
  have hread1 : m2.readAt out 256 = Memory.spliceBits (m1.readAt out 256) 8 (bits.extractLsb' 8 8) := by
    simpa only [m2, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 1#64) hf1 (hr.no_wrap (k := 1) (by decide))
        (by decide) (bits.extractLsb' 8 8))
  let m3 := m2.storeAt (out.add 2) (bits.extractLsb' 16 8)
  have hf3 : Fits m3 out 256 := hf2.storeAt
  have hread2 : m3.readAt out 256 = Memory.spliceBits (m2.readAt out 256) 16 (bits.extractLsb' 16 8) := by
    simpa only [m3, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 2#64) hf2 (hr.no_wrap (k := 2) (by decide))
        (by decide) (bits.extractLsb' 16 8))
  let m4 := m3.storeAt (out.add 3) (bits.extractLsb' 24 8)
  have hf4 : Fits m4 out 256 := hf3.storeAt
  have hread3 : m4.readAt out 256 = Memory.spliceBits (m3.readAt out 256) 24 (bits.extractLsb' 24 8) := by
    simpa only [m4, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 3#64) hf3 (hr.no_wrap (k := 3) (by decide))
        (by decide) (bits.extractLsb' 24 8))
  let m5 := m4.storeAt (out.add 4) (bits.extractLsb' 32 8)
  have hf5 : Fits m5 out 256 := hf4.storeAt
  have hread4 : m5.readAt out 256 = Memory.spliceBits (m4.readAt out 256) 32 (bits.extractLsb' 32 8) := by
    simpa only [m5, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 4#64) hf4 (hr.no_wrap (k := 4) (by decide))
        (by decide) (bits.extractLsb' 32 8))
  let m6 := m5.storeAt (out.add 5) (bits.extractLsb' 40 8)
  have hf6 : Fits m6 out 256 := hf5.storeAt
  have hread5 : m6.readAt out 256 = Memory.spliceBits (m5.readAt out 256) 40 (bits.extractLsb' 40 8) := by
    simpa only [m6, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 5#64) hf5 (hr.no_wrap (k := 5) (by decide))
        (by decide) (bits.extractLsb' 40 8))
  let m7 := m6.storeAt (out.add 6) (bits.extractLsb' 48 8)
  have hf7 : Fits m7 out 256 := hf6.storeAt
  have hread6 : m7.readAt out 256 = Memory.spliceBits (m6.readAt out 256) 48 (bits.extractLsb' 48 8) := by
    simpa only [m7, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 6#64) hf6 (hr.no_wrap (k := 6) (by decide))
        (by decide) (bits.extractLsb' 48 8))
  let m8 := m7.storeAt (out.add 7) (bits.extractLsb' 56 8)
  have hf8 : Fits m8 out 256 := hf7.storeAt
  have hread7 : m8.readAt out 256 = Memory.spliceBits (m7.readAt out 256) 56 (bits.extractLsb' 56 8) := by
    simpa only [m8, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 7#64) hf7 (hr.no_wrap (k := 7) (by decide))
        (by decide) (bits.extractLsb' 56 8))
  let m9 := m8.storeAt (out.add 8) (bits.extractLsb' 64 8)
  have hf9 : Fits m9 out 256 := hf8.storeAt
  have hread8 : m9.readAt out 256 = Memory.spliceBits (m8.readAt out 256) 64 (bits.extractLsb' 64 8) := by
    simpa only [m9, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 8#64) hf8 (hr.no_wrap (k := 8) (by decide))
        (by decide) (bits.extractLsb' 64 8))
  let m10 := m9.storeAt (out.add 9) (bits.extractLsb' 72 8)
  have hf10 : Fits m10 out 256 := hf9.storeAt
  have hread9 : m10.readAt out 256 = Memory.spliceBits (m9.readAt out 256) 72 (bits.extractLsb' 72 8) := by
    simpa only [m10, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 9#64) hf9 (hr.no_wrap (k := 9) (by decide))
        (by decide) (bits.extractLsb' 72 8))
  let m11 := m10.storeAt (out.add 10) (bits.extractLsb' 80 8)
  have hf11 : Fits m11 out 256 := hf10.storeAt
  have hread10 : m11.readAt out 256 = Memory.spliceBits (m10.readAt out 256) 80 (bits.extractLsb' 80 8) := by
    simpa only [m11, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 10#64) hf10 (hr.no_wrap (k := 10) (by decide))
        (by decide) (bits.extractLsb' 80 8))
  let m12 := m11.storeAt (out.add 11) (bits.extractLsb' 88 8)
  have hf12 : Fits m12 out 256 := hf11.storeAt
  have hread11 : m12.readAt out 256 = Memory.spliceBits (m11.readAt out 256) 88 (bits.extractLsb' 88 8) := by
    simpa only [m12, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 11#64) hf11 (hr.no_wrap (k := 11) (by decide))
        (by decide) (bits.extractLsb' 88 8))
  let m13 := m12.storeAt (out.add 12) (bits.extractLsb' 96 8)
  have hf13 : Fits m13 out 256 := hf12.storeAt
  have hread12 : m13.readAt out 256 = Memory.spliceBits (m12.readAt out 256) 96 (bits.extractLsb' 96 8) := by
    simpa only [m13, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 12#64) hf12 (hr.no_wrap (k := 12) (by decide))
        (by decide) (bits.extractLsb' 96 8))
  let m14 := m13.storeAt (out.add 13) (bits.extractLsb' 104 8)
  have hf14 : Fits m14 out 256 := hf13.storeAt
  have hread13 : m14.readAt out 256 = Memory.spliceBits (m13.readAt out 256) 104 (bits.extractLsb' 104 8) := by
    simpa only [m14, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 13#64) hf13 (hr.no_wrap (k := 13) (by decide))
        (by decide) (bits.extractLsb' 104 8))
  let m15 := m14.storeAt (out.add 14) (bits.extractLsb' 112 8)
  have hf15 : Fits m15 out 256 := hf14.storeAt
  have hread14 : m15.readAt out 256 = Memory.spliceBits (m14.readAt out 256) 112 (bits.extractLsb' 112 8) := by
    simpa only [m15, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 14#64) hf14 (hr.no_wrap (k := 14) (by decide))
        (by decide) (bits.extractLsb' 112 8))
  let m16 := m15.storeAt (out.add 15) (bits.extractLsb' 120 8)
  have hf16 : Fits m16 out 256 := hf15.storeAt
  have hread15 : m16.readAt out 256 = Memory.spliceBits (m15.readAt out 256) 120 (bits.extractLsb' 120 8) := by
    simpa only [m16, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 15#64) hf15 (hr.no_wrap (k := 15) (by decide))
        (by decide) (bits.extractLsb' 120 8))
  let m17 := m16.storeAt (out.add 16) (bits.extractLsb' 128 8)
  have hf17 : Fits m17 out 256 := hf16.storeAt
  have hread16 : m17.readAt out 256 = Memory.spliceBits (m16.readAt out 256) 128 (bits.extractLsb' 128 8) := by
    simpa only [m17, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 16#64) hf16 (hr.no_wrap (k := 16) (by decide))
        (by decide) (bits.extractLsb' 128 8))
  let m18 := m17.storeAt (out.add 17) (bits.extractLsb' 136 8)
  have hf18 : Fits m18 out 256 := hf17.storeAt
  have hread17 : m18.readAt out 256 = Memory.spliceBits (m17.readAt out 256) 136 (bits.extractLsb' 136 8) := by
    simpa only [m18, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 17#64) hf17 (hr.no_wrap (k := 17) (by decide))
        (by decide) (bits.extractLsb' 136 8))
  let m19 := m18.storeAt (out.add 18) (bits.extractLsb' 144 8)
  have hf19 : Fits m19 out 256 := hf18.storeAt
  have hread18 : m19.readAt out 256 = Memory.spliceBits (m18.readAt out 256) 144 (bits.extractLsb' 144 8) := by
    simpa only [m19, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 18#64) hf18 (hr.no_wrap (k := 18) (by decide))
        (by decide) (bits.extractLsb' 144 8))
  let m20 := m19.storeAt (out.add 19) (bits.extractLsb' 152 8)
  have hf20 : Fits m20 out 256 := hf19.storeAt
  have hread19 : m20.readAt out 256 = Memory.spliceBits (m19.readAt out 256) 152 (bits.extractLsb' 152 8) := by
    simpa only [m20, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 19#64) hf19 (hr.no_wrap (k := 19) (by decide))
        (by decide) (bits.extractLsb' 152 8))
  let m21 := m20.storeAt (out.add 20) (bits.extractLsb' 160 8)
  have hf21 : Fits m21 out 256 := hf20.storeAt
  have hread20 : m21.readAt out 256 = Memory.spliceBits (m20.readAt out 256) 160 (bits.extractLsb' 160 8) := by
    simpa only [m21, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 20#64) hf20 (hr.no_wrap (k := 20) (by decide))
        (by decide) (bits.extractLsb' 160 8))
  let m22 := m21.storeAt (out.add 21) (bits.extractLsb' 168 8)
  have hf22 : Fits m22 out 256 := hf21.storeAt
  have hread21 : m22.readAt out 256 = Memory.spliceBits (m21.readAt out 256) 168 (bits.extractLsb' 168 8) := by
    simpa only [m22, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 21#64) hf21 (hr.no_wrap (k := 21) (by decide))
        (by decide) (bits.extractLsb' 168 8))
  let m23 := m22.storeAt (out.add 22) (bits.extractLsb' 176 8)
  have hf23 : Fits m23 out 256 := hf22.storeAt
  have hread22 : m23.readAt out 256 = Memory.spliceBits (m22.readAt out 256) 176 (bits.extractLsb' 176 8) := by
    simpa only [m23, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 22#64) hf22 (hr.no_wrap (k := 22) (by decide))
        (by decide) (bits.extractLsb' 176 8))
  let m24 := m23.storeAt (out.add 23) (bits.extractLsb' 184 8)
  have hf24 : Fits m24 out 256 := hf23.storeAt
  have hread23 : m24.readAt out 256 = Memory.spliceBits (m23.readAt out 256) 184 (bits.extractLsb' 184 8) := by
    simpa only [m24, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 23#64) hf23 (hr.no_wrap (k := 23) (by decide))
        (by decide) (bits.extractLsb' 184 8))
  let m25 := m24.storeAt (out.add 24) (bits.extractLsb' 192 8)
  have hf25 : Fits m25 out 256 := hf24.storeAt
  have hread24 : m25.readAt out 256 = Memory.spliceBits (m24.readAt out 256) 192 (bits.extractLsb' 192 8) := by
    simpa only [m25, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 24#64) hf24 (hr.no_wrap (k := 24) (by decide))
        (by decide) (bits.extractLsb' 192 8))
  let m26 := m25.storeAt (out.add 25) (bits.extractLsb' 200 8)
  have hf26 : Fits m26 out 256 := hf25.storeAt
  have hread25 : m26.readAt out 256 = Memory.spliceBits (m25.readAt out 256) 200 (bits.extractLsb' 200 8) := by
    simpa only [m26, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 25#64) hf25 (hr.no_wrap (k := 25) (by decide))
        (by decide) (bits.extractLsb' 200 8))
  let m27 := m26.storeAt (out.add 26) (bits.extractLsb' 208 8)
  have hf27 : Fits m27 out 256 := hf26.storeAt
  have hread26 : m27.readAt out 256 = Memory.spliceBits (m26.readAt out 256) 208 (bits.extractLsb' 208 8) := by
    simpa only [m27, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 26#64) hf26 (hr.no_wrap (k := 26) (by decide))
        (by decide) (bits.extractLsb' 208 8))
  let m28 := m27.storeAt (out.add 27) (bits.extractLsb' 216 8)
  have hf28 : Fits m28 out 256 := hf27.storeAt
  have hread27 : m28.readAt out 256 = Memory.spliceBits (m27.readAt out 256) 216 (bits.extractLsb' 216 8) := by
    simpa only [m28, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 27#64) hf27 (hr.no_wrap (k := 27) (by decide))
        (by decide) (bits.extractLsb' 216 8))
  let m29 := m28.storeAt (out.add 28) (bits.extractLsb' 224 8)
  have hf29 : Fits m29 out 256 := hf28.storeAt
  have hread28 : m29.readAt out 256 = Memory.spliceBits (m28.readAt out 256) 224 (bits.extractLsb' 224 8) := by
    simpa only [m29, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 28#64) hf28 (hr.no_wrap (k := 28) (by decide))
        (by decide) (bits.extractLsb' 224 8))
  let m30 := m29.storeAt (out.add 29) (bits.extractLsb' 232 8)
  have hf30 : Fits m30 out 256 := hf29.storeAt
  have hread29 : m30.readAt out 256 = Memory.spliceBits (m29.readAt out 256) 232 (bits.extractLsb' 232 8) := by
    simpa only [m30, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 29#64) hf29 (hr.no_wrap (k := 29) (by decide))
        (by decide) (bits.extractLsb' 232 8))
  let m31 := m30.storeAt (out.add 30) (bits.extractLsb' 240 8)
  have hf31 : Fits m31 out 256 := hf30.storeAt
  have hread30 : m31.readAt out 256 = Memory.spliceBits (m30.readAt out 256) 240 (bits.extractLsb' 240 8) := by
    simpa only [m31, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 30#64) hf30 (hr.no_wrap (k := 30) (by decide))
        (by decide) (bits.extractLsb' 240 8))
  let m32 := m31.storeAt (out.add 31) (bits.extractLsb' 248 8)
  have hf32 : Fits m32 out 256 := hf31.storeAt
  have hread31 : m32.readAt out 256 = Memory.spliceBits (m31.readAt out 256) 248 (bits.extractLsb' 248 8) := by
    simpa only [m32, Pointer.add_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] using
      (MemoryState.readAt_add_storeAt (off := 31#64) hf31 (hr.no_wrap (k := 31) (by decide))
        (by decide) (bits.extractLsb' 248 8))
  change m32.readAt out 256 = bits
  rw [hread31, hread30, hread29, hread28, hread27, hread26, hread25, hread24, hread23, hread22, hread21, hread20, hread19, hread18, hread17, hread16, hread15, hread14, hread13, hread12, hread11, hread10, hread9, hread8, hread7, hread6, hread5, hread4, hread3, hread2, hread1, hread0]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Memory.getLsbD_spliceBits, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

end Agave.Ed25519.Encoding.Compress.Execution

import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputFieldFlags
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-! Actual mixed-width loads and assembly of one 64-bit input chunk.
Every shift flag and disjoint OR is proved from its fragment bit intervals. -/

set_option maxRecDepth 100000

namespace Agave.Ed25519.Verifier.Execution.ScalarWide

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

def inputChunk6Env (E : Env program.Γ) (mem : MemoryState) (input : Pointer) : Env program.Γ :=
  let v216 : Pointer := input.add 48#64
  let v217 : BitVec 16 := mem.readAt (input.add 48#64) 16
  let v218 : BitVec 64 := v217.setWidth 64
  let v219 : Pointer := input.add 50#64
  let v220 : BitVec 8 := mem.readAt (input.add 50#64) 8
  let v221 : BitVec 64 := v220.setWidth 64
  let v222 : BitVec 64 := v221 <<< 16
  let v223 : BitVec 64 := v222 ||| v218
  let v224 : Pointer := input.add 51#64
  let v225 : BitVec 8 := mem.readAt (input.add 51#64) 8
  let v226 : BitVec 64 := v225.setWidth 64
  let v227 : BitVec 64 := v226 <<< 24
  let v228 : BitVec 64 := v223 ||| v227
  let v229 : Pointer := input.add 52#64
  let v230 : BitVec 16 := mem.readAt (input.add 52#64) 16
  let v231 : BitVec 64 := v230.setWidth 64
  let v232 : BitVec 64 := v231 <<< 32
  let v233 : Pointer := input.add 54#64
  let v234 : BitVec 16 := mem.readAt (input.add 54#64) 16
  let v235 : BitVec 64 := v234.setWidth 64
  let v236 : BitVec 64 := v235 <<< 48
  let v237 : BitVec 64 := v232 ||| v236
  let v238 : BitVec 64 := v237 ||| v228
  E[%216 := .value v216,
    %217 := .value v217,
    %218 := .value v218,
    %219 := .value v219,
    %220 := .value v220,
    %221 := .value v221,
    %222 := .value v222,
    %223 := .value v223,
    %224 := .value v224,
    %225 := .value v225,
    %226 := .value v226,
    %227 := .value v227,
    %228 := .value v228,
    %229 := .value v229,
    %230 := .value v230,
    %231 := .value v231,
    %232 := .value v232,
    %233 := .value v233,
    %234 := .value v234,
    %235 := .value v235,
    %236 := .value v236,
    %237 := .value v237,
    %238 := .value v238]

def inputChunk6Word (mem : MemoryState) (input : Pointer) : BitVec 64 :=
  let v216 : Pointer := input.add 48#64
  let v217 : BitVec 16 := mem.readAt (input.add 48#64) 16
  let v218 : BitVec 64 := v217.setWidth 64
  let v219 : Pointer := input.add 50#64
  let v220 : BitVec 8 := mem.readAt (input.add 50#64) 8
  let v221 : BitVec 64 := v220.setWidth 64
  let v222 : BitVec 64 := v221 <<< 16
  let v223 : BitVec 64 := v222 ||| v218
  let v224 : Pointer := input.add 51#64
  let v225 : BitVec 8 := mem.readAt (input.add 51#64) 8
  let v226 : BitVec 64 := v225.setWidth 64
  let v227 : BitVec 64 := v226 <<< 24
  let v228 : BitVec 64 := v223 ||| v227
  let v229 : Pointer := input.add 52#64
  let v230 : BitVec 16 := mem.readAt (input.add 52#64) 16
  let v231 : BitVec 64 := v230.setWidth 64
  let v232 : BitVec 64 := v231 <<< 32
  let v233 : Pointer := input.add 54#64
  let v234 : BitVec 16 := mem.readAt (input.add 54#64) 16
  let v235 : BitVec 64 := v234.setWidth 64
  let v236 : BitVec 64 := v235 <<< 48
  let v237 : BitVec 64 := v232 ||| v236
  let v238 : BitVec 64 := v237 ||| v228
  v238

theorem inputChunk6_run (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (input : Pointer)
    (hinput : E.read (%arg1) = .value input)
    (hlive : SmallRange state.mem input 64)
    (hc2 : E.read (%2) = .value 32#64)
    (hc6 : E.read (%6) = .value 48#64)
    (hc13 : E.read (%13) = .value 16#64)
    (hc16 : E.read (%16) = .value 24#64)
    (hc30 : E.read (%30) = .value 50#64)
    (hc31 : E.read (%31) = .value 51#64)
    (hc32 : E.read (%32) = .value 52#64)
    (hc33 : E.read (%33) = .value 54#64)
    (scratch : Pointer)
    (hscratch : E.read (%82) = .value scratch)
    (hfits : Fits state.mem scratch 64)
    : List.foldlM Instr.run E (((program.entry p g).body.drop 236).take 24) state =
      .value (inputChunk6Env E state.mem input,
        {state with mem := state.mem.storeAt scratch (inputChunk6Word state.mem input)}) := by
  change E.args 1 = .value input at hinput
  have hg48 := hlive.gep (k := 48) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (48 : Int)] =
    .value (input.add 48#64) at hg48
  have hg50 := hlive.gep (k := 50) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (50 : Int)] =
    .value (input.add 50#64) at hg50
  have hg51 := hlive.gep (k := 51) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (51 : Int)] =
    .value (input.add 51#64) at hg51
  have hg52 := hlive.gep (k := 52) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (52 : Int)] =
    .value (input.add 52#64) at hg52
  have hg54 := hlive.gep (k := 54) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (54 : Int)] =
    .value (input.add 54#64) at hg54
  have hf217 := hlive.fits_add (k := 48) (count := 2) (by decide)
  have hf220 := hlive.fits_add (k := 50) (count := 1) (by decide)
  have hf225 := hlive.fits_add (k := 51) (count := 1) (by decide)
  have hf230 := hlive.fits_add (k := 52) (count := 2) (by decide)
  have hf234 := hlive.fits_add (k := 54) (count := 2) (by decide)
  have hs222 := field_shl_nsw_nuw (state.mem.readAt (input.add 50#64) 8) 16 (by decide) (by decide)
  have hs227 := field_shl_nsw_nuw (state.mem.readAt (input.add 51#64) 8) 24 (by decide) (by decide)
  have hs232 := field_shl_nsw_nuw (state.mem.readAt (input.add 52#64) 16) 32 (by decide) (by decide)
  have hs236 := field_shl_nuw (state.mem.readAt (input.add 54#64) 16) 48 (by decide) (by decide)
  have hd223 : ((state.mem.readAt (input.add 50#64) 8).setWidth 64 <<< 16) &&& (state.mem.readAt (input.add 48#64) 16).setWidth 64 = 0 := by
    have hp : (placedField (state.mem.readAt (input.add 50#64) 8) 16) &&& (placedField (state.mem.readAt (input.add 48#64) 16) 0) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 50#64) 8) (state.mem.readAt (input.add 48#64) 16) 16 0 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  have hd228 : (((state.mem.readAt (input.add 50#64) 8).setWidth 64 <<< 16) ||| (state.mem.readAt (input.add 48#64) 16).setWidth 64) &&& ((state.mem.readAt (input.add 51#64) 8).setWidth 64 <<< 24) = 0 := by
    have hp : ((placedField (state.mem.readAt (input.add 50#64) 8) 16) ||| (placedField (state.mem.readAt (input.add 48#64) 16) 0)) &&& (placedField (state.mem.readAt (input.add 51#64) 8) 24) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 50#64) 8) (state.mem.readAt (input.add 51#64) 8) 16 24 (by decide)
      have h1_0 := placedField_disjoint (state.mem.readAt (input.add 48#64) 16) (state.mem.readAt (input.add 51#64) 8) 0 24 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, h1_0, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  have hd237 : ((state.mem.readAt (input.add 52#64) 16).setWidth 64 <<< 32) &&& ((state.mem.readAt (input.add 54#64) 16).setWidth 64 <<< 48) = 0 := by
    have hp : (placedField (state.mem.readAt (input.add 52#64) 16) 32) &&& (placedField (state.mem.readAt (input.add 54#64) 16) 48) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 52#64) 16) (state.mem.readAt (input.add 54#64) 16) 32 48 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  have hd238 : (((state.mem.readAt (input.add 52#64) 16).setWidth 64 <<< 32) ||| ((state.mem.readAt (input.add 54#64) 16).setWidth 64 <<< 48)) &&& ((((state.mem.readAt (input.add 50#64) 8).setWidth 64 <<< 16) ||| (state.mem.readAt (input.add 48#64) 16).setWidth 64) ||| ((state.mem.readAt (input.add 51#64) 8).setWidth 64 <<< 24)) = 0 := by
    have hp : ((placedField (state.mem.readAt (input.add 52#64) 16) 32) ||| (placedField (state.mem.readAt (input.add 54#64) 16) 48)) &&& (((placedField (state.mem.readAt (input.add 50#64) 8) 16) ||| (placedField (state.mem.readAt (input.add 48#64) 16) 0)) ||| (placedField (state.mem.readAt (input.add 51#64) 8) 24)) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 52#64) 16) (state.mem.readAt (input.add 50#64) 8) 32 16 (by decide)
      have h0_1 := placedField_disjoint (state.mem.readAt (input.add 52#64) 16) (state.mem.readAt (input.add 48#64) 16) 32 0 (by decide)
      have h0_2 := placedField_disjoint (state.mem.readAt (input.add 52#64) 16) (state.mem.readAt (input.add 51#64) 8) 32 24 (by decide)
      have h1_0 := placedField_disjoint (state.mem.readAt (input.add 54#64) 16) (state.mem.readAt (input.add 50#64) 8) 48 16 (by decide)
      have h1_1 := placedField_disjoint (state.mem.readAt (input.add 54#64) 16) (state.mem.readAt (input.add 48#64) 16) 48 0 (by decide)
      have h1_2 := placedField_disjoint (state.mem.readAt (input.add 54#64) 16) (state.mem.readAt (input.add 51#64) 8) 48 24 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, h0_1, h0_2, h1_0, h1_1, h1_2, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    inputChunk6Env, inputChunk6Word,
    hinput, hc2, hc6, hc13, hc16, hc30, hc31, hc32, hc33, hg48, hg50, hg51, hg52, hg54, hf217, hf220, hf225, hf230, hf234, hs222, hs227, hs232, hs236, hd223, hd228, hd237, hd238, hscratch, hfits,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    placedField, Operation.load, Operation.store, Operation.zext, Operation.or,
    UnOp.compute, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.Verifier.Execution.ScalarWide

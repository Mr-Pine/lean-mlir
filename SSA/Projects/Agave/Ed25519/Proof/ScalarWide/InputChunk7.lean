import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputFieldFlags
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-! Actual mixed-width loads and assembly of one 64-bit input chunk.
Every shift flag and disjoint OR is proved from its fragment bit intervals. -/

set_option maxRecDepth 100000

namespace Agave.Ed25519.Verifier.Execution.ScalarWide

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

def inputChunk7Env (E : Env program.Γ) (mem : MemoryState) (input : Pointer) : Env program.Γ :=
  let v239 : Pointer := input.add 56#64
  let v240 : BitVec 16 := mem.readAt (input.add 56#64) 16
  let v241 : BitVec 64 := v240.setWidth 64
  let v242 : Pointer := input.add 58#64
  let v243 : BitVec 8 := mem.readAt (input.add 58#64) 8
  let v244 : BitVec 64 := v243.setWidth 64
  let v245 : BitVec 64 := v244 <<< 16
  let v246 : BitVec 64 := v245 ||| v241
  let v247 : Pointer := input.add 59#64
  let v248 : BitVec 8 := mem.readAt (input.add 59#64) 8
  let v249 : BitVec 64 := v248.setWidth 64
  let v250 : BitVec 64 := v249 <<< 24
  let v251 : Pointer := input.add 60#64
  let v252 : BitVec 16 := mem.readAt (input.add 60#64) 16
  let v253 : BitVec 64 := v252.setWidth 64
  let v254 : BitVec 64 := v253 <<< 32
  let v255 : BitVec 64 := v250 ||| v254
  let v256 : Pointer := input.add 62#64
  let v257 : BitVec 16 := mem.readAt (input.add 62#64) 16
  let v258 : BitVec 64 := v257.setWidth 64
  let v259 : BitVec 64 := v258 <<< 48
  let v260 : BitVec 64 := v255 ||| v259
  let v261 : BitVec 64 := v260 ||| v246
  E[%239 := .value v239,
    %240 := .value v240,
    %241 := .value v241,
    %242 := .value v242,
    %243 := .value v243,
    %244 := .value v244,
    %245 := .value v245,
    %246 := .value v246,
    %247 := .value v247,
    %248 := .value v248,
    %249 := .value v249,
    %250 := .value v250,
    %251 := .value v251,
    %252 := .value v252,
    %253 := .value v253,
    %254 := .value v254,
    %255 := .value v255,
    %256 := .value v256,
    %257 := .value v257,
    %258 := .value v258,
    %259 := .value v259,
    %260 := .value v260,
    %261 := .value v261]

def inputChunk7Word (mem : MemoryState) (input : Pointer) : BitVec 64 :=
  let v239 : Pointer := input.add 56#64
  let v240 : BitVec 16 := mem.readAt (input.add 56#64) 16
  let v241 : BitVec 64 := v240.setWidth 64
  let v242 : Pointer := input.add 58#64
  let v243 : BitVec 8 := mem.readAt (input.add 58#64) 8
  let v244 : BitVec 64 := v243.setWidth 64
  let v245 : BitVec 64 := v244 <<< 16
  let v246 : BitVec 64 := v245 ||| v241
  let v247 : Pointer := input.add 59#64
  let v248 : BitVec 8 := mem.readAt (input.add 59#64) 8
  let v249 : BitVec 64 := v248.setWidth 64
  let v250 : BitVec 64 := v249 <<< 24
  let v251 : Pointer := input.add 60#64
  let v252 : BitVec 16 := mem.readAt (input.add 60#64) 16
  let v253 : BitVec 64 := v252.setWidth 64
  let v254 : BitVec 64 := v253 <<< 32
  let v255 : BitVec 64 := v250 ||| v254
  let v256 : Pointer := input.add 62#64
  let v257 : BitVec 16 := mem.readAt (input.add 62#64) 16
  let v258 : BitVec 64 := v257.setWidth 64
  let v259 : BitVec 64 := v258 <<< 48
  let v260 : BitVec 64 := v255 ||| v259
  let v261 : BitVec 64 := v260 ||| v246
  v261

theorem inputChunk7_run (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (input : Pointer)
    (hinput : E.read (%arg1) = .value input)
    (hlive : SmallRange state.mem input 64)
    (hc2 : E.read (%2) = .value 32#64)
    (hc6 : E.read (%6) = .value 48#64)
    (hc8 : E.read (%8) = .value 56#64)
    (hc13 : E.read (%13) = .value 16#64)
    (hc16 : E.read (%16) = .value 24#64)
    (hc34 : E.read (%34) = .value 58#64)
    (hc35 : E.read (%35) = .value 59#64)
    (hc36 : E.read (%36) = .value 60#64)
    (hc37 : E.read (%37) = .value 62#64)
    (scratch : Pointer)
    (hscratch : E.read (%83) = .value scratch)
    (hfits : Fits state.mem scratch 64)
    : List.foldlM Instr.run E (((program.entry p g).body.drop 260).take 24) state =
      .value (inputChunk7Env E state.mem input,
        {state with mem := state.mem.storeAt scratch (inputChunk7Word state.mem input)}) := by
  change E.args 1 = .value input at hinput
  have hg56 := hlive.gep (k := 56) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (56 : Int)] =
    .value (input.add 56#64) at hg56
  have hg58 := hlive.gep (k := 58) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (58 : Int)] =
    .value (input.add 58#64) at hg58
  have hg59 := hlive.gep (k := 59) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (59 : Int)] =
    .value (input.add 59#64) at hg59
  have hg60 := hlive.gep (k := 60) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (60 : Int)] =
    .value (input.add 60#64) at hg60
  have hg62 := hlive.gep (k := 62) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (62 : Int)] =
    .value (input.add 62#64) at hg62
  have hf240 := hlive.fits_add (k := 56) (count := 2) (by decide)
  have hf243 := hlive.fits_add (k := 58) (count := 1) (by decide)
  have hf248 := hlive.fits_add (k := 59) (count := 1) (by decide)
  have hf252 := hlive.fits_add (k := 60) (count := 2) (by decide)
  have hf257 := hlive.fits_add (k := 62) (count := 2) (by decide)
  have hs245 := field_shl_nsw_nuw (state.mem.readAt (input.add 58#64) 8) 16 (by decide) (by decide)
  have hs250 := field_shl_nsw_nuw (state.mem.readAt (input.add 59#64) 8) 24 (by decide) (by decide)
  have hs254 := field_shl_nsw_nuw (state.mem.readAt (input.add 60#64) 16) 32 (by decide) (by decide)
  have hs259 := field_shl_nuw (state.mem.readAt (input.add 62#64) 16) 48 (by decide) (by decide)
  have hd246 : ((state.mem.readAt (input.add 58#64) 8).setWidth 64 <<< 16) &&& (state.mem.readAt (input.add 56#64) 16).setWidth 64 = 0 := by
    have hp : (placedField (state.mem.readAt (input.add 58#64) 8) 16) &&& (placedField (state.mem.readAt (input.add 56#64) 16) 0) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 58#64) 8) (state.mem.readAt (input.add 56#64) 16) 16 0 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  have hd255 : ((state.mem.readAt (input.add 59#64) 8).setWidth 64 <<< 24) &&& ((state.mem.readAt (input.add 60#64) 16).setWidth 64 <<< 32) = 0 := by
    have hp : (placedField (state.mem.readAt (input.add 59#64) 8) 24) &&& (placedField (state.mem.readAt (input.add 60#64) 16) 32) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 59#64) 8) (state.mem.readAt (input.add 60#64) 16) 24 32 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  have hd260 : (((state.mem.readAt (input.add 59#64) 8).setWidth 64 <<< 24) ||| ((state.mem.readAt (input.add 60#64) 16).setWidth 64 <<< 32)) &&& ((state.mem.readAt (input.add 62#64) 16).setWidth 64 <<< 48) = 0 := by
    have hp : ((placedField (state.mem.readAt (input.add 59#64) 8) 24) ||| (placedField (state.mem.readAt (input.add 60#64) 16) 32)) &&& (placedField (state.mem.readAt (input.add 62#64) 16) 48) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 59#64) 8) (state.mem.readAt (input.add 62#64) 16) 24 48 (by decide)
      have h1_0 := placedField_disjoint (state.mem.readAt (input.add 60#64) 16) (state.mem.readAt (input.add 62#64) 16) 32 48 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, h1_0, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  have hd261 : ((((state.mem.readAt (input.add 59#64) 8).setWidth 64 <<< 24) ||| ((state.mem.readAt (input.add 60#64) 16).setWidth 64 <<< 32)) ||| ((state.mem.readAt (input.add 62#64) 16).setWidth 64 <<< 48)) &&& (((state.mem.readAt (input.add 58#64) 8).setWidth 64 <<< 16) ||| (state.mem.readAt (input.add 56#64) 16).setWidth 64) = 0 := by
    have hp : (((placedField (state.mem.readAt (input.add 59#64) 8) 24) ||| (placedField (state.mem.readAt (input.add 60#64) 16) 32)) ||| (placedField (state.mem.readAt (input.add 62#64) 16) 48)) &&& ((placedField (state.mem.readAt (input.add 58#64) 8) 16) ||| (placedField (state.mem.readAt (input.add 56#64) 16) 0)) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 59#64) 8) (state.mem.readAt (input.add 58#64) 8) 24 16 (by decide)
      have h0_1 := placedField_disjoint (state.mem.readAt (input.add 59#64) 8) (state.mem.readAt (input.add 56#64) 16) 24 0 (by decide)
      have h1_0 := placedField_disjoint (state.mem.readAt (input.add 60#64) 16) (state.mem.readAt (input.add 58#64) 8) 32 16 (by decide)
      have h1_1 := placedField_disjoint (state.mem.readAt (input.add 60#64) 16) (state.mem.readAt (input.add 56#64) 16) 32 0 (by decide)
      have h2_0 := placedField_disjoint (state.mem.readAt (input.add 62#64) 16) (state.mem.readAt (input.add 58#64) 8) 48 16 (by decide)
      have h2_1 := placedField_disjoint (state.mem.readAt (input.add 62#64) 16) (state.mem.readAt (input.add 56#64) 16) 48 0 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, h0_1, h1_0, h1_1, h2_0, h2_1, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    inputChunk7Env, inputChunk7Word,
    hinput, hc2, hc6, hc8, hc13, hc16, hc34, hc35, hc36, hc37, hg56, hg58, hg59, hg60, hg62, hf240, hf243, hf248, hf252, hf257, hs245, hs250, hs254, hs259, hd246, hd255, hd260, hd261, hscratch, hfits,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    placedField, Operation.load, Operation.store, Operation.zext, Operation.or,
    UnOp.compute, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.Verifier.Execution.ScalarWide

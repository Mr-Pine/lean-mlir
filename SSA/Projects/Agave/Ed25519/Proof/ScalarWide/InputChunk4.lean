import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputFieldFlags
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-! Actual mixed-width loads and assembly of one 64-bit input chunk.
Every shift flag and disjoint OR is proved from its fragment bit intervals. -/

set_option maxRecDepth 100000

namespace Agave.Ed25519.Verifier.Execution.ScalarWide

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

def inputChunk4Env (E : Env program.Γ) (mem : MemoryState) (input : Pointer) : Env program.Γ :=
  let v175 : Pointer := input.add 32#64
  let v176 : BitVec 8 := mem.readAt (input.add 32#64) 8
  let v177 : BitVec 64 := v176.setWidth 64
  let v178 : Pointer := input.add 33#64
  let v179 : BitVec 8 := mem.readAt (input.add 33#64) 8
  let v180 : BitVec 64 := v179.setWidth 64
  let v181 : BitVec 64 := v180 <<< 8
  let v182 : Pointer := input.add 34#64
  let v183 : BitVec 16 := mem.readAt (input.add 34#64) 16
  let v184 : BitVec 64 := v183.setWidth 64
  let v185 : BitVec 64 := v184 <<< 16
  let v186 : BitVec 64 := v181 ||| v185
  let v187 : Pointer := input.add 36#64
  let v188 : BitVec 16 := mem.readAt (input.add 36#64) 16
  let v189 : BitVec 64 := v188.setWidth 64
  let v190 : BitVec 64 := v189 <<< 32
  let v191 : BitVec 64 := v186 ||| v190
  let v192 : Pointer := input.add 38#64
  let v193 : BitVec 16 := mem.readAt (input.add 38#64) 16
  let v194 : BitVec 64 := v193.setWidth 64
  let v195 : BitVec 64 := v194 <<< 48
  let v196 : BitVec 64 := v191 ||| v195
  let v197 : BitVec 64 := v196 ||| v177
  E[%175 := .value v175,
    %176 := .value v176,
    %177 := .value v177,
    %178 := .value v178,
    %179 := .value v179,
    %180 := .value v180,
    %181 := .value v181,
    %182 := .value v182,
    %183 := .value v183,
    %184 := .value v184,
    %185 := .value v185,
    %186 := .value v186,
    %187 := .value v187,
    %188 := .value v188,
    %189 := .value v189,
    %190 := .value v190,
    %191 := .value v191,
    %192 := .value v192,
    %193 := .value v193,
    %194 := .value v194,
    %195 := .value v195,
    %196 := .value v196,
    %197 := .value v197]

def inputChunk4Word (mem : MemoryState) (input : Pointer) : BitVec 64 :=
  let v175 : Pointer := input.add 32#64
  let v176 : BitVec 8 := mem.readAt (input.add 32#64) 8
  let v177 : BitVec 64 := v176.setWidth 64
  let v178 : Pointer := input.add 33#64
  let v179 : BitVec 8 := mem.readAt (input.add 33#64) 8
  let v180 : BitVec 64 := v179.setWidth 64
  let v181 : BitVec 64 := v180 <<< 8
  let v182 : Pointer := input.add 34#64
  let v183 : BitVec 16 := mem.readAt (input.add 34#64) 16
  let v184 : BitVec 64 := v183.setWidth 64
  let v185 : BitVec 64 := v184 <<< 16
  let v186 : BitVec 64 := v181 ||| v185
  let v187 : Pointer := input.add 36#64
  let v188 : BitVec 16 := mem.readAt (input.add 36#64) 16
  let v189 : BitVec 64 := v188.setWidth 64
  let v190 : BitVec 64 := v189 <<< 32
  let v191 : BitVec 64 := v186 ||| v190
  let v192 : Pointer := input.add 38#64
  let v193 : BitVec 16 := mem.readAt (input.add 38#64) 16
  let v194 : BitVec 64 := v193.setWidth 64
  let v195 : BitVec 64 := v194 <<< 48
  let v196 : BitVec 64 := v191 ||| v195
  let v197 : BitVec 64 := v196 ||| v177
  v197

theorem inputChunk4_run (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (input : Pointer)
    (hinput : E.read (%arg1) = .value input)
    (hlive : SmallRange state.mem input 64)
    (hc2 : E.read (%2) = .value 32#64)
    (hc6 : E.read (%6) = .value 48#64)
    (hc9 : E.read (%9) = .value 8#64)
    (hc13 : E.read (%13) = .value 16#64)
    (hc23 : E.read (%23) = .value 33#64)
    (hc24 : E.read (%24) = .value 34#64)
    (hc25 : E.read (%25) = .value 36#64)
    (hc26 : E.read (%26) = .value 38#64)
    (scratch : Pointer)
    (hscratch : E.read (%80) = .value scratch)
    (hfits : Fits state.mem scratch 64)
    : List.foldlM Instr.run E (((program.entry p g).body.drop 193).take 24) state =
      .value (inputChunk4Env E state.mem input,
        {state with mem := state.mem.storeAt scratch (inputChunk4Word state.mem input)}) := by
  change E.args 1 = .value input at hinput
  have hg32 := hlive.gep (k := 32) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (32 : Int)] =
    .value (input.add 32#64) at hg32
  have hg33 := hlive.gep (k := 33) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (33 : Int)] =
    .value (input.add 33#64) at hg33
  have hg34 := hlive.gep (k := 34) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (34 : Int)] =
    .value (input.add 34#64) at hg34
  have hg36 := hlive.gep (k := 36) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (36 : Int)] =
    .value (input.add 36#64) at hg36
  have hg38 := hlive.gep (k := 38) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (38 : Int)] =
    .value (input.add 38#64) at hg38
  have hf176 := hlive.fits_add (k := 32) (count := 1) (by decide)
  have hf179 := hlive.fits_add (k := 33) (count := 1) (by decide)
  have hf183 := hlive.fits_add (k := 34) (count := 2) (by decide)
  have hf188 := hlive.fits_add (k := 36) (count := 2) (by decide)
  have hf193 := hlive.fits_add (k := 38) (count := 2) (by decide)
  have hs181 := field_shl_nsw_nuw (state.mem.readAt (input.add 33#64) 8) 8 (by decide) (by decide)
  have hs185 := field_shl_nsw_nuw (state.mem.readAt (input.add 34#64) 16) 16 (by decide) (by decide)
  have hs190 := field_shl_nsw_nuw (state.mem.readAt (input.add 36#64) 16) 32 (by decide) (by decide)
  have hs195 := field_shl_nuw (state.mem.readAt (input.add 38#64) 16) 48 (by decide) (by decide)
  have hd186 : ((state.mem.readAt (input.add 33#64) 8).setWidth 64 <<< 8) &&& ((state.mem.readAt (input.add 34#64) 16).setWidth 64 <<< 16) = 0 := by
    have hp : (placedField (state.mem.readAt (input.add 33#64) 8) 8) &&& (placedField (state.mem.readAt (input.add 34#64) 16) 16) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 33#64) 8) (state.mem.readAt (input.add 34#64) 16) 8 16 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  have hd191 : (((state.mem.readAt (input.add 33#64) 8).setWidth 64 <<< 8) ||| ((state.mem.readAt (input.add 34#64) 16).setWidth 64 <<< 16)) &&& ((state.mem.readAt (input.add 36#64) 16).setWidth 64 <<< 32) = 0 := by
    have hp : ((placedField (state.mem.readAt (input.add 33#64) 8) 8) ||| (placedField (state.mem.readAt (input.add 34#64) 16) 16)) &&& (placedField (state.mem.readAt (input.add 36#64) 16) 32) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 33#64) 8) (state.mem.readAt (input.add 36#64) 16) 8 32 (by decide)
      have h1_0 := placedField_disjoint (state.mem.readAt (input.add 34#64) 16) (state.mem.readAt (input.add 36#64) 16) 16 32 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, h1_0, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  have hd196 : ((((state.mem.readAt (input.add 33#64) 8).setWidth 64 <<< 8) ||| ((state.mem.readAt (input.add 34#64) 16).setWidth 64 <<< 16)) ||| ((state.mem.readAt (input.add 36#64) 16).setWidth 64 <<< 32)) &&& ((state.mem.readAt (input.add 38#64) 16).setWidth 64 <<< 48) = 0 := by
    have hp : (((placedField (state.mem.readAt (input.add 33#64) 8) 8) ||| (placedField (state.mem.readAt (input.add 34#64) 16) 16)) ||| (placedField (state.mem.readAt (input.add 36#64) 16) 32)) &&& (placedField (state.mem.readAt (input.add 38#64) 16) 48) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 33#64) 8) (state.mem.readAt (input.add 38#64) 16) 8 48 (by decide)
      have h1_0 := placedField_disjoint (state.mem.readAt (input.add 34#64) 16) (state.mem.readAt (input.add 38#64) 16) 16 48 (by decide)
      have h2_0 := placedField_disjoint (state.mem.readAt (input.add 36#64) 16) (state.mem.readAt (input.add 38#64) 16) 32 48 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, h1_0, h2_0, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  have hd197 : (((((state.mem.readAt (input.add 33#64) 8).setWidth 64 <<< 8) ||| ((state.mem.readAt (input.add 34#64) 16).setWidth 64 <<< 16)) ||| ((state.mem.readAt (input.add 36#64) 16).setWidth 64 <<< 32)) ||| ((state.mem.readAt (input.add 38#64) 16).setWidth 64 <<< 48)) &&& (state.mem.readAt (input.add 32#64) 8).setWidth 64 = 0 := by
    have hp : ((((placedField (state.mem.readAt (input.add 33#64) 8) 8) ||| (placedField (state.mem.readAt (input.add 34#64) 16) 16)) ||| (placedField (state.mem.readAt (input.add 36#64) 16) 32)) ||| (placedField (state.mem.readAt (input.add 38#64) 16) 48)) &&& (placedField (state.mem.readAt (input.add 32#64) 8) 0) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 33#64) 8) (state.mem.readAt (input.add 32#64) 8) 8 0 (by decide)
      have h1_0 := placedField_disjoint (state.mem.readAt (input.add 34#64) 16) (state.mem.readAt (input.add 32#64) 8) 16 0 (by decide)
      have h2_0 := placedField_disjoint (state.mem.readAt (input.add 36#64) 16) (state.mem.readAt (input.add 32#64) 8) 32 0 (by decide)
      have h3_0 := placedField_disjoint (state.mem.readAt (input.add 38#64) 16) (state.mem.readAt (input.add 32#64) 8) 48 0 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, h1_0, h2_0, h3_0, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    inputChunk4Env, inputChunk4Word,
    hinput, hc2, hc6, hc9, hc13, hc23, hc24, hc25, hc26, hg32, hg33, hg34, hg36, hg38, hf176, hf179, hf183, hf188, hf193, hs181, hs185, hs190, hs195, hd186, hd191, hd196, hd197, hscratch, hfits,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    placedField, Operation.load, Operation.store, Operation.zext, Operation.or,
    UnOp.compute, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.Verifier.Execution.ScalarWide

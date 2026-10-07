import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputFieldFlags
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-! Actual mixed-width loads and assembly of one 64-bit input chunk.
Every shift flag and disjoint OR is proved from its fragment bit intervals. -/

set_option maxRecDepth 100000

namespace Agave.Ed25519.Verifier.Execution.ScalarWide

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

def inputChunk5Env (E : Env program.Γ) (mem : MemoryState) (input : Pointer) : Env program.Γ :=
  let v198 : Pointer := input.add 40#64
  let v199 : BitVec 32 := mem.readAt (input.add 40#64) 32
  let v200 : BitVec 64 := v199.setWidth 64
  let v201 : Pointer := input.add 44#64
  let v202 : BitVec 8 := mem.readAt (input.add 44#64) 8
  let v203 : BitVec 64 := v202.setWidth 64
  let v204 : BitVec 64 := v203 <<< 32
  let v205 : BitVec 64 := v204 ||| v200
  let v206 : Pointer := input.add 45#64
  let v207 : BitVec 8 := mem.readAt (input.add 45#64) 8
  let v208 : BitVec 64 := v207.setWidth 64
  let v209 : BitVec 64 := v208 <<< 40
  let v210 : BitVec 64 := v205 ||| v209
  let v211 : Pointer := input.add 46#64
  let v212 : BitVec 16 := mem.readAt (input.add 46#64) 16
  let v213 : BitVec 64 := v212.setWidth 64
  let v214 : BitVec 64 := v213 <<< 48
  let v215 : BitVec 64 := v214 ||| v210
  E[%198 := .value v198,
    %199 := .value v199,
    %200 := .value v200,
    %201 := .value v201,
    %202 := .value v202,
    %203 := .value v203,
    %204 := .value v204,
    %205 := .value v205,
    %206 := .value v206,
    %207 := .value v207,
    %208 := .value v208,
    %209 := .value v209,
    %210 := .value v210,
    %211 := .value v211,
    %212 := .value v212,
    %213 := .value v213,
    %214 := .value v214,
    %215 := .value v215]

def inputChunk5Word (mem : MemoryState) (input : Pointer) : BitVec 64 :=
  let v198 : Pointer := input.add 40#64
  let v199 : BitVec 32 := mem.readAt (input.add 40#64) 32
  let v200 : BitVec 64 := v199.setWidth 64
  let v201 : Pointer := input.add 44#64
  let v202 : BitVec 8 := mem.readAt (input.add 44#64) 8
  let v203 : BitVec 64 := v202.setWidth 64
  let v204 : BitVec 64 := v203 <<< 32
  let v205 : BitVec 64 := v204 ||| v200
  let v206 : Pointer := input.add 45#64
  let v207 : BitVec 8 := mem.readAt (input.add 45#64) 8
  let v208 : BitVec 64 := v207.setWidth 64
  let v209 : BitVec 64 := v208 <<< 40
  let v210 : BitVec 64 := v205 ||| v209
  let v211 : Pointer := input.add 46#64
  let v212 : BitVec 16 := mem.readAt (input.add 46#64) 16
  let v213 : BitVec 64 := v212.setWidth 64
  let v214 : BitVec 64 := v213 <<< 48
  let v215 : BitVec 64 := v214 ||| v210
  v215

theorem inputChunk5_run (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (input : Pointer)
    (hinput : E.read (%arg1) = .value input)
    (hlive : SmallRange state.mem input 64)
    (hc2 : E.read (%2) = .value 32#64)
    (hc4 : E.read (%4) = .value 40#64)
    (hc6 : E.read (%6) = .value 48#64)
    (hc27 : E.read (%27) = .value 44#64)
    (hc28 : E.read (%28) = .value 45#64)
    (hc29 : E.read (%29) = .value 46#64)
    (scratch : Pointer)
    (hscratch : E.read (%81) = .value scratch)
    (hfits : Fits state.mem scratch 64)
    : List.foldlM Instr.run E (((program.entry p g).body.drop 217).take 19) state =
      .value (inputChunk5Env E state.mem input,
        {state with mem := state.mem.storeAt scratch (inputChunk5Word state.mem input)}) := by
  change E.args 1 = .value input at hinput
  have hg40 := hlive.gep (k := 40) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (40 : Int)] =
    .value (input.add 40#64) at hg40
  have hg44 := hlive.gep (k := 44) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (44 : Int)] =
    .value (input.add 44#64) at hg44
  have hg45 := hlive.gep (k := 45) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (45 : Int)] =
    .value (input.add 45#64) at hg45
  have hg46 := hlive.gep (k := 46) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (46 : Int)] =
    .value (input.add 46#64) at hg46
  have hf199 := hlive.fits_add (k := 40) (count := 4) (by decide)
  have hf202 := hlive.fits_add (k := 44) (count := 1) (by decide)
  have hf207 := hlive.fits_add (k := 45) (count := 1) (by decide)
  have hf212 := hlive.fits_add (k := 46) (count := 2) (by decide)
  have hs204 := field_shl_nsw_nuw (state.mem.readAt (input.add 44#64) 8) 32 (by decide) (by decide)
  have hs209 := field_shl_nsw_nuw (state.mem.readAt (input.add 45#64) 8) 40 (by decide) (by decide)
  have hs214 := field_shl_nuw (state.mem.readAt (input.add 46#64) 16) 48 (by decide) (by decide)
  have hd205 : ((state.mem.readAt (input.add 44#64) 8).setWidth 64 <<< 32) &&& (state.mem.readAt (input.add 40#64) 32).setWidth 64 = 0 := by
    have hp : (placedField (state.mem.readAt (input.add 44#64) 8) 32) &&& (placedField (state.mem.readAt (input.add 40#64) 32) 0) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 44#64) 8) (state.mem.readAt (input.add 40#64) 32) 32 0 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  have hd210 : (((state.mem.readAt (input.add 44#64) 8).setWidth 64 <<< 32) ||| (state.mem.readAt (input.add 40#64) 32).setWidth 64) &&& ((state.mem.readAt (input.add 45#64) 8).setWidth 64 <<< 40) = 0 := by
    have hp : ((placedField (state.mem.readAt (input.add 44#64) 8) 32) ||| (placedField (state.mem.readAt (input.add 40#64) 32) 0)) &&& (placedField (state.mem.readAt (input.add 45#64) 8) 40) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 44#64) 8) (state.mem.readAt (input.add 45#64) 8) 32 40 (by decide)
      have h1_0 := placedField_disjoint (state.mem.readAt (input.add 40#64) 32) (state.mem.readAt (input.add 45#64) 8) 0 40 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, h1_0, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  have hd215 : ((state.mem.readAt (input.add 46#64) 16).setWidth 64 <<< 48) &&& ((((state.mem.readAt (input.add 44#64) 8).setWidth 64 <<< 32) ||| (state.mem.readAt (input.add 40#64) 32).setWidth 64) ||| ((state.mem.readAt (input.add 45#64) 8).setWidth 64 <<< 40)) = 0 := by
    have hp : (placedField (state.mem.readAt (input.add 46#64) 16) 48) &&& (((placedField (state.mem.readAt (input.add 44#64) 8) 32) ||| (placedField (state.mem.readAt (input.add 40#64) 32) 0)) ||| (placedField (state.mem.readAt (input.add 45#64) 8) 40)) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 46#64) 16) (state.mem.readAt (input.add 44#64) 8) 48 32 (by decide)
      have h0_1 := placedField_disjoint (state.mem.readAt (input.add 46#64) 16) (state.mem.readAt (input.add 40#64) 32) 48 0 (by decide)
      have h0_2 := placedField_disjoint (state.mem.readAt (input.add 46#64) 16) (state.mem.readAt (input.add 45#64) 8) 48 40 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, h0_1, h0_2, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    inputChunk5Env, inputChunk5Word,
    hinput, hc2, hc4, hc6, hc27, hc28, hc29, hg40, hg44, hg45, hg46, hf199, hf202, hf207, hf212, hs204, hs209, hs214, hd205, hd210, hd215, hscratch, hfits,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    placedField, Operation.load, Operation.store, Operation.zext, Operation.or,
    UnOp.compute, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.Verifier.Execution.ScalarWide

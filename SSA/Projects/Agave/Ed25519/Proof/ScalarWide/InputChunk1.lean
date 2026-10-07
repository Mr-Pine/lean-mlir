import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputFieldFlags
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-! Actual mixed-width loads and assembly of one 64-bit input chunk.
Every shift flag and disjoint OR is proved from its fragment bit intervals. -/

set_option maxRecDepth 100000

namespace Agave.Ed25519.Verifier.Execution.ScalarWide

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

def inputChunk1Env (E : Env program.Γ) (mem : MemoryState) (input : Pointer) : Env program.Γ :=
  let v111 : Pointer := input.add 8#64
  let v112 : BitVec 32 := mem.readAt (input.add 8#64) 32
  let v113 : BitVec 64 := v112.setWidth 64
  let v114 : Pointer := input.add 12#64
  let v115 : BitVec 8 := mem.readAt (input.add 12#64) 8
  let v116 : BitVec 64 := v115.setWidth 64
  let v117 : BitVec 64 := v116 <<< 32
  let v118 : BitVec 64 := v117 ||| v113
  let v119 : Pointer := input.add 13#64
  let v120 : BitVec 8 := mem.readAt (input.add 13#64) 8
  let v121 : BitVec 64 := v120.setWidth 64
  let v122 : BitVec 64 := v121 <<< 40
  let v123 : Pointer := input.add 14#64
  let v124 : BitVec 16 := mem.readAt (input.add 14#64) 16
  let v125 : BitVec 64 := v124.setWidth 64
  let v126 : BitVec 64 := v125 <<< 48
  let v127 : BitVec 64 := v122 ||| v126
  let v128 : BitVec 64 := v127 ||| v118
  E[%111 := .value v111,
    %112 := .value v112,
    %113 := .value v113,
    %114 := .value v114,
    %115 := .value v115,
    %116 := .value v116,
    %117 := .value v117,
    %118 := .value v118,
    %119 := .value v119,
    %120 := .value v120,
    %121 := .value v121,
    %122 := .value v122,
    %123 := .value v123,
    %124 := .value v124,
    %125 := .value v125,
    %126 := .value v126,
    %127 := .value v127,
    %128 := .value v128]

def inputChunk1Word (mem : MemoryState) (input : Pointer) : BitVec 64 :=
  let v111 : Pointer := input.add 8#64
  let v112 : BitVec 32 := mem.readAt (input.add 8#64) 32
  let v113 : BitVec 64 := v112.setWidth 64
  let v114 : Pointer := input.add 12#64
  let v115 : BitVec 8 := mem.readAt (input.add 12#64) 8
  let v116 : BitVec 64 := v115.setWidth 64
  let v117 : BitVec 64 := v116 <<< 32
  let v118 : BitVec 64 := v117 ||| v113
  let v119 : Pointer := input.add 13#64
  let v120 : BitVec 8 := mem.readAt (input.add 13#64) 8
  let v121 : BitVec 64 := v120.setWidth 64
  let v122 : BitVec 64 := v121 <<< 40
  let v123 : Pointer := input.add 14#64
  let v124 : BitVec 16 := mem.readAt (input.add 14#64) 16
  let v125 : BitVec 64 := v124.setWidth 64
  let v126 : BitVec 64 := v125 <<< 48
  let v127 : BitVec 64 := v122 ||| v126
  let v128 : BitVec 64 := v127 ||| v118
  v128

theorem inputChunk1_run (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (input : Pointer)
    (hinput : E.read (%arg1) = .value input)
    (hlive : SmallRange state.mem input 64)
    (hc2 : E.read (%2) = .value 32#64)
    (hc4 : E.read (%4) = .value 40#64)
    (hc6 : E.read (%6) = .value 48#64)
    (hc9 : E.read (%9) = .value 8#64)
    (hc10 : E.read (%10) = .value 12#64)
    (hc11 : E.read (%11) = .value 13#64)
    (hc12 : E.read (%12) = .value 14#64)
    (scratch : Pointer)
    (hscratch : E.read (%77) = .value scratch)
    (hfits : Fits state.mem scratch 64)
    : List.foldlM Instr.run E (((program.entry p g).body.drop 126).take 19) state =
      .value (inputChunk1Env E state.mem input,
        {state with mem := state.mem.storeAt scratch (inputChunk1Word state.mem input)}) := by
  change E.args 1 = .value input at hinput
  have hg8 := hlive.gep (k := 8) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (8 : Int)] =
    .value (input.add 8#64) at hg8
  have hg12 := hlive.gep (k := 12) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (12 : Int)] =
    .value (input.add 12#64) at hg12
  have hg13 := hlive.gep (k := 13) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (13 : Int)] =
    .value (input.add 13#64) at hg13
  have hg14 := hlive.gep (k := 14) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (14 : Int)] =
    .value (input.add 14#64) at hg14
  have hf112 := hlive.fits_add (k := 8) (count := 4) (by decide)
  have hf115 := hlive.fits_add (k := 12) (count := 1) (by decide)
  have hf120 := hlive.fits_add (k := 13) (count := 1) (by decide)
  have hf124 := hlive.fits_add (k := 14) (count := 2) (by decide)
  have hs117 := field_shl_nsw_nuw (state.mem.readAt (input.add 12#64) 8) 32 (by decide) (by decide)
  have hs122 := field_shl_nsw_nuw (state.mem.readAt (input.add 13#64) 8) 40 (by decide) (by decide)
  have hs126 := field_shl_nuw (state.mem.readAt (input.add 14#64) 16) 48 (by decide) (by decide)
  have hd118 : ((state.mem.readAt (input.add 12#64) 8).setWidth 64 <<< 32) &&& (state.mem.readAt (input.add 8#64) 32).setWidth 64 = 0 := by
    have hp : (placedField (state.mem.readAt (input.add 12#64) 8) 32) &&& (placedField (state.mem.readAt (input.add 8#64) 32) 0) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 12#64) 8) (state.mem.readAt (input.add 8#64) 32) 32 0 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  have hd127 : ((state.mem.readAt (input.add 13#64) 8).setWidth 64 <<< 40) &&& ((state.mem.readAt (input.add 14#64) 16).setWidth 64 <<< 48) = 0 := by
    have hp : (placedField (state.mem.readAt (input.add 13#64) 8) 40) &&& (placedField (state.mem.readAt (input.add 14#64) 16) 48) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 13#64) 8) (state.mem.readAt (input.add 14#64) 16) 40 48 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  have hd128 : (((state.mem.readAt (input.add 13#64) 8).setWidth 64 <<< 40) ||| ((state.mem.readAt (input.add 14#64) 16).setWidth 64 <<< 48)) &&& (((state.mem.readAt (input.add 12#64) 8).setWidth 64 <<< 32) ||| (state.mem.readAt (input.add 8#64) 32).setWidth 64) = 0 := by
    have hp : ((placedField (state.mem.readAt (input.add 13#64) 8) 40) ||| (placedField (state.mem.readAt (input.add 14#64) 16) 48)) &&& ((placedField (state.mem.readAt (input.add 12#64) 8) 32) ||| (placedField (state.mem.readAt (input.add 8#64) 32) 0)) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 13#64) 8) (state.mem.readAt (input.add 12#64) 8) 40 32 (by decide)
      have h0_1 := placedField_disjoint (state.mem.readAt (input.add 13#64) 8) (state.mem.readAt (input.add 8#64) 32) 40 0 (by decide)
      have h1_0 := placedField_disjoint (state.mem.readAt (input.add 14#64) 16) (state.mem.readAt (input.add 12#64) 8) 48 32 (by decide)
      have h1_1 := placedField_disjoint (state.mem.readAt (input.add 14#64) 16) (state.mem.readAt (input.add 8#64) 32) 48 0 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, h0_1, h1_0, h1_1, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    inputChunk1Env, inputChunk1Word,
    hinput, hc2, hc4, hc6, hc9, hc10, hc11, hc12, hg8, hg12, hg13, hg14, hf112, hf115, hf120, hf124, hs117, hs122, hs126, hd118, hd127, hd128, hscratch, hfits,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    placedField, Operation.load, Operation.store, Operation.zext, Operation.or,
    UnOp.compute, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.Verifier.Execution.ScalarWide

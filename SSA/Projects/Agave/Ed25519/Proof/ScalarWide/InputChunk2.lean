import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputFieldFlags
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-! Actual mixed-width loads and assembly of one 64-bit input chunk.
Every shift flag and disjoint OR is proved from its fragment bit intervals. -/

set_option maxRecDepth 100000

namespace Agave.Ed25519.Verifier.Execution.ScalarWide

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

def inputChunk2Env (E : Env program.Γ) (mem : MemoryState) (input : Pointer) : Env program.Γ :=
  let v129 : Pointer := input.add 16#64
  let v130 : BitVec 16 := mem.readAt (input.add 16#64) 16
  let v131 : BitVec 64 := v130.setWidth 64
  let v132 : Pointer := input.add 18#64
  let v133 : BitVec 8 := mem.readAt (input.add 18#64) 8
  let v134 : BitVec 64 := v133.setWidth 64
  let v135 : BitVec 64 := v134 <<< 16
  let v136 : BitVec 64 := v135 ||| v131
  let v137 : Pointer := input.add 19#64
  let v138 : BitVec 8 := mem.readAt (input.add 19#64) 8
  let v139 : BitVec 64 := v138.setWidth 64
  let v140 : BitVec 64 := v139 <<< 24
  let v141 : BitVec 64 := v136 ||| v140
  let v142 : Pointer := input.add 20#64
  let v143 : BitVec 16 := mem.readAt (input.add 20#64) 16
  let v144 : BitVec 64 := v143.setWidth 64
  let v145 : BitVec 64 := v144 <<< 32
  let v146 : Pointer := input.add 22#64
  let v147 : BitVec 16 := mem.readAt (input.add 22#64) 16
  let v148 : BitVec 64 := v147.setWidth 64
  let v149 : BitVec 64 := v148 <<< 48
  let v150 : BitVec 64 := v145 ||| v149
  let v151 : BitVec 64 := v150 ||| v141
  E[%129 := .value v129,
    %130 := .value v130,
    %131 := .value v131,
    %132 := .value v132,
    %133 := .value v133,
    %134 := .value v134,
    %135 := .value v135,
    %136 := .value v136,
    %137 := .value v137,
    %138 := .value v138,
    %139 := .value v139,
    %140 := .value v140,
    %141 := .value v141,
    %142 := .value v142,
    %143 := .value v143,
    %144 := .value v144,
    %145 := .value v145,
    %146 := .value v146,
    %147 := .value v147,
    %148 := .value v148,
    %149 := .value v149,
    %150 := .value v150,
    %151 := .value v151]

def inputChunk2Word (mem : MemoryState) (input : Pointer) : BitVec 64 :=
  let v129 : Pointer := input.add 16#64
  let v130 : BitVec 16 := mem.readAt (input.add 16#64) 16
  let v131 : BitVec 64 := v130.setWidth 64
  let v132 : Pointer := input.add 18#64
  let v133 : BitVec 8 := mem.readAt (input.add 18#64) 8
  let v134 : BitVec 64 := v133.setWidth 64
  let v135 : BitVec 64 := v134 <<< 16
  let v136 : BitVec 64 := v135 ||| v131
  let v137 : Pointer := input.add 19#64
  let v138 : BitVec 8 := mem.readAt (input.add 19#64) 8
  let v139 : BitVec 64 := v138.setWidth 64
  let v140 : BitVec 64 := v139 <<< 24
  let v141 : BitVec 64 := v136 ||| v140
  let v142 : Pointer := input.add 20#64
  let v143 : BitVec 16 := mem.readAt (input.add 20#64) 16
  let v144 : BitVec 64 := v143.setWidth 64
  let v145 : BitVec 64 := v144 <<< 32
  let v146 : Pointer := input.add 22#64
  let v147 : BitVec 16 := mem.readAt (input.add 22#64) 16
  let v148 : BitVec 64 := v147.setWidth 64
  let v149 : BitVec 64 := v148 <<< 48
  let v150 : BitVec 64 := v145 ||| v149
  let v151 : BitVec 64 := v150 ||| v141
  v151

theorem inputChunk2_run (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (input : Pointer)
    (hinput : E.read (%arg1) = .value input)
    (hlive : SmallRange state.mem input 64)
    (hc2 : E.read (%2) = .value 32#64)
    (hc6 : E.read (%6) = .value 48#64)
    (hc13 : E.read (%13) = .value 16#64)
    (hc14 : E.read (%14) = .value 18#64)
    (hc15 : E.read (%15) = .value 19#64)
    (hc16 : E.read (%16) = .value 24#64)
    (hc17 : E.read (%17) = .value 20#64)
    (hc18 : E.read (%18) = .value 22#64)
    (scratch : Pointer)
    (hscratch : E.read (%78) = .value scratch)
    (hfits : Fits state.mem scratch 64)
    : List.foldlM Instr.run E (((program.entry p g).body.drop 145).take 24) state =
      .value (inputChunk2Env E state.mem input,
        {state with mem := state.mem.storeAt scratch (inputChunk2Word state.mem input)}) := by
  change E.args 1 = .value input at hinput
  have hg16 := hlive.gep (k := 16) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (16 : Int)] =
    .value (input.add 16#64) at hg16
  have hg18 := hlive.gep (k := 18) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (18 : Int)] =
    .value (input.add 18#64) at hg18
  have hg19 := hlive.gep (k := 19) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (19 : Int)] =
    .value (input.add 19#64) at hg19
  have hg20 := hlive.gep (k := 20) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (20 : Int)] =
    .value (input.add 20#64) at hg20
  have hg22 := hlive.gep (k := 22) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (22 : Int)] =
    .value (input.add 22#64) at hg22
  have hf130 := hlive.fits_add (k := 16) (count := 2) (by decide)
  have hf133 := hlive.fits_add (k := 18) (count := 1) (by decide)
  have hf138 := hlive.fits_add (k := 19) (count := 1) (by decide)
  have hf143 := hlive.fits_add (k := 20) (count := 2) (by decide)
  have hf147 := hlive.fits_add (k := 22) (count := 2) (by decide)
  have hs135 := field_shl_nsw_nuw (state.mem.readAt (input.add 18#64) 8) 16 (by decide) (by decide)
  have hs140 := field_shl_nsw_nuw (state.mem.readAt (input.add 19#64) 8) 24 (by decide) (by decide)
  have hs145 := field_shl_nsw_nuw (state.mem.readAt (input.add 20#64) 16) 32 (by decide) (by decide)
  have hs149 := field_shl_nuw (state.mem.readAt (input.add 22#64) 16) 48 (by decide) (by decide)
  have hd136 : ((state.mem.readAt (input.add 18#64) 8).setWidth 64 <<< 16) &&& (state.mem.readAt (input.add 16#64) 16).setWidth 64 = 0 := by
    have hp : (placedField (state.mem.readAt (input.add 18#64) 8) 16) &&& (placedField (state.mem.readAt (input.add 16#64) 16) 0) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 18#64) 8) (state.mem.readAt (input.add 16#64) 16) 16 0 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  have hd141 : (((state.mem.readAt (input.add 18#64) 8).setWidth 64 <<< 16) ||| (state.mem.readAt (input.add 16#64) 16).setWidth 64) &&& ((state.mem.readAt (input.add 19#64) 8).setWidth 64 <<< 24) = 0 := by
    have hp : ((placedField (state.mem.readAt (input.add 18#64) 8) 16) ||| (placedField (state.mem.readAt (input.add 16#64) 16) 0)) &&& (placedField (state.mem.readAt (input.add 19#64) 8) 24) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 18#64) 8) (state.mem.readAt (input.add 19#64) 8) 16 24 (by decide)
      have h1_0 := placedField_disjoint (state.mem.readAt (input.add 16#64) 16) (state.mem.readAt (input.add 19#64) 8) 0 24 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, h1_0, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  have hd150 : ((state.mem.readAt (input.add 20#64) 16).setWidth 64 <<< 32) &&& ((state.mem.readAt (input.add 22#64) 16).setWidth 64 <<< 48) = 0 := by
    have hp : (placedField (state.mem.readAt (input.add 20#64) 16) 32) &&& (placedField (state.mem.readAt (input.add 22#64) 16) 48) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 20#64) 16) (state.mem.readAt (input.add 22#64) 16) 32 48 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  have hd151 : (((state.mem.readAt (input.add 20#64) 16).setWidth 64 <<< 32) ||| ((state.mem.readAt (input.add 22#64) 16).setWidth 64 <<< 48)) &&& ((((state.mem.readAt (input.add 18#64) 8).setWidth 64 <<< 16) ||| (state.mem.readAt (input.add 16#64) 16).setWidth 64) ||| ((state.mem.readAt (input.add 19#64) 8).setWidth 64 <<< 24)) = 0 := by
    have hp : ((placedField (state.mem.readAt (input.add 20#64) 16) 32) ||| (placedField (state.mem.readAt (input.add 22#64) 16) 48)) &&& (((placedField (state.mem.readAt (input.add 18#64) 8) 16) ||| (placedField (state.mem.readAt (input.add 16#64) 16) 0)) ||| (placedField (state.mem.readAt (input.add 19#64) 8) 24)) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 20#64) 16) (state.mem.readAt (input.add 18#64) 8) 32 16 (by decide)
      have h0_1 := placedField_disjoint (state.mem.readAt (input.add 20#64) 16) (state.mem.readAt (input.add 16#64) 16) 32 0 (by decide)
      have h0_2 := placedField_disjoint (state.mem.readAt (input.add 20#64) 16) (state.mem.readAt (input.add 19#64) 8) 32 24 (by decide)
      have h1_0 := placedField_disjoint (state.mem.readAt (input.add 22#64) 16) (state.mem.readAt (input.add 18#64) 8) 48 16 (by decide)
      have h1_1 := placedField_disjoint (state.mem.readAt (input.add 22#64) 16) (state.mem.readAt (input.add 16#64) 16) 48 0 (by decide)
      have h1_2 := placedField_disjoint (state.mem.readAt (input.add 22#64) 16) (state.mem.readAt (input.add 19#64) 8) 48 24 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, h0_1, h0_2, h1_0, h1_1, h1_2, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    inputChunk2Env, inputChunk2Word,
    hinput, hc2, hc6, hc13, hc14, hc15, hc16, hc17, hc18, hg16, hg18, hg19, hg20, hg22, hf130, hf133, hf138, hf143, hf147, hs135, hs140, hs145, hs149, hd136, hd141, hd150, hd151, hscratch, hfits,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    placedField, Operation.load, Operation.store, Operation.zext, Operation.or,
    UnOp.compute, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.Verifier.Execution.ScalarWide

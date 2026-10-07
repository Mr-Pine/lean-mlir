import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputFieldFlags
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-! Actual mixed-width loads and assembly of one 64-bit input chunk.
Every shift flag and disjoint OR is proved from its fragment bit intervals. -/

set_option maxRecDepth 100000

namespace Agave.Ed25519.Verifier.Execution.ScalarWide

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

def inputChunk3Env (E : Env program.Γ) (mem : MemoryState) (input : Pointer) : Env program.Γ :=
  let v152 : Pointer := input.add 24#64
  let v153 : BitVec 8 := mem.readAt (input.add 24#64) 8
  let v154 : BitVec 64 := v153.setWidth 64
  let v155 : Pointer := input.add 25#64
  let v156 : BitVec 8 := mem.readAt (input.add 25#64) 8
  let v157 : BitVec 64 := v156.setWidth 64
  let v158 : BitVec 64 := v157 <<< 8
  let v159 : BitVec 64 := v158 ||| v154
  let v160 : Pointer := input.add 26#64
  let v161 : BitVec 16 := mem.readAt (input.add 26#64) 16
  let v162 : BitVec 64 := v161.setWidth 64
  let v163 : BitVec 64 := v162 <<< 16
  let v164 : Pointer := input.add 28#64
  let v165 : BitVec 16 := mem.readAt (input.add 28#64) 16
  let v166 : BitVec 64 := v165.setWidth 64
  let v167 : BitVec 64 := v166 <<< 32
  let v168 : BitVec 64 := v163 ||| v167
  let v169 : Pointer := input.add 30#64
  let v170 : BitVec 16 := mem.readAt (input.add 30#64) 16
  let v171 : BitVec 64 := v170.setWidth 64
  let v172 : BitVec 64 := v171 <<< 48
  let v173 : BitVec 64 := v168 ||| v172
  let v174 : BitVec 64 := v173 ||| v159
  E[%152 := .value v152,
    %153 := .value v153,
    %154 := .value v154,
    %155 := .value v155,
    %156 := .value v156,
    %157 := .value v157,
    %158 := .value v158,
    %159 := .value v159,
    %160 := .value v160,
    %161 := .value v161,
    %162 := .value v162,
    %163 := .value v163,
    %164 := .value v164,
    %165 := .value v165,
    %166 := .value v166,
    %167 := .value v167,
    %168 := .value v168,
    %169 := .value v169,
    %170 := .value v170,
    %171 := .value v171,
    %172 := .value v172,
    %173 := .value v173,
    %174 := .value v174]

def inputChunk3Word (mem : MemoryState) (input : Pointer) : BitVec 64 :=
  let v152 : Pointer := input.add 24#64
  let v153 : BitVec 8 := mem.readAt (input.add 24#64) 8
  let v154 : BitVec 64 := v153.setWidth 64
  let v155 : Pointer := input.add 25#64
  let v156 : BitVec 8 := mem.readAt (input.add 25#64) 8
  let v157 : BitVec 64 := v156.setWidth 64
  let v158 : BitVec 64 := v157 <<< 8
  let v159 : BitVec 64 := v158 ||| v154
  let v160 : Pointer := input.add 26#64
  let v161 : BitVec 16 := mem.readAt (input.add 26#64) 16
  let v162 : BitVec 64 := v161.setWidth 64
  let v163 : BitVec 64 := v162 <<< 16
  let v164 : Pointer := input.add 28#64
  let v165 : BitVec 16 := mem.readAt (input.add 28#64) 16
  let v166 : BitVec 64 := v165.setWidth 64
  let v167 : BitVec 64 := v166 <<< 32
  let v168 : BitVec 64 := v163 ||| v167
  let v169 : Pointer := input.add 30#64
  let v170 : BitVec 16 := mem.readAt (input.add 30#64) 16
  let v171 : BitVec 64 := v170.setWidth 64
  let v172 : BitVec 64 := v171 <<< 48
  let v173 : BitVec 64 := v168 ||| v172
  let v174 : BitVec 64 := v173 ||| v159
  v174

theorem inputChunk3_run (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (input : Pointer)
    (hinput : E.read (%arg1) = .value input)
    (hlive : SmallRange state.mem input 64)
    (hc2 : E.read (%2) = .value 32#64)
    (hc6 : E.read (%6) = .value 48#64)
    (hc9 : E.read (%9) = .value 8#64)
    (hc13 : E.read (%13) = .value 16#64)
    (hc16 : E.read (%16) = .value 24#64)
    (hc19 : E.read (%19) = .value 25#64)
    (hc20 : E.read (%20) = .value 26#64)
    (hc21 : E.read (%21) = .value 28#64)
    (hc22 : E.read (%22) = .value 30#64)
    (scratch : Pointer)
    (hscratch : E.read (%79) = .value scratch)
    (hfits : Fits state.mem scratch 64)
    : List.foldlM Instr.run E (((program.entry p g).body.drop 169).take 24) state =
      .value (inputChunk3Env E state.mem input,
        {state with mem := state.mem.storeAt scratch (inputChunk3Word state.mem input)}) := by
  change E.args 1 = .value input at hinput
  have hg24 := hlive.gep (k := 24) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (24 : Int)] =
    .value (input.add 24#64) at hg24
  have hg25 := hlive.gep (k := 25) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (25 : Int)] =
    .value (input.add 25#64) at hg25
  have hg26 := hlive.gep (k := 26) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (26 : Int)] =
    .value (input.add 26#64) at hg26
  have hg28 := hlive.gep (k := 28) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (28 : Int)] =
    .value (input.add 28#64) at hg28
  have hg30 := hlive.gep (k := 30) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (30 : Int)] =
    .value (input.add 30#64) at hg30
  have hf153 := hlive.fits_add (k := 24) (count := 1) (by decide)
  have hf156 := hlive.fits_add (k := 25) (count := 1) (by decide)
  have hf161 := hlive.fits_add (k := 26) (count := 2) (by decide)
  have hf165 := hlive.fits_add (k := 28) (count := 2) (by decide)
  have hf170 := hlive.fits_add (k := 30) (count := 2) (by decide)
  have hs158 := field_shl_nsw_nuw (state.mem.readAt (input.add 25#64) 8) 8 (by decide) (by decide)
  have hs163 := field_shl_nsw_nuw (state.mem.readAt (input.add 26#64) 16) 16 (by decide) (by decide)
  have hs167 := field_shl_nsw_nuw (state.mem.readAt (input.add 28#64) 16) 32 (by decide) (by decide)
  have hs172 := field_shl_nuw (state.mem.readAt (input.add 30#64) 16) 48 (by decide) (by decide)
  have hd159 : ((state.mem.readAt (input.add 25#64) 8).setWidth 64 <<< 8) &&& (state.mem.readAt (input.add 24#64) 8).setWidth 64 = 0 := by
    have hp : (placedField (state.mem.readAt (input.add 25#64) 8) 8) &&& (placedField (state.mem.readAt (input.add 24#64) 8) 0) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 25#64) 8) (state.mem.readAt (input.add 24#64) 8) 8 0 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  have hd168 : ((state.mem.readAt (input.add 26#64) 16).setWidth 64 <<< 16) &&& ((state.mem.readAt (input.add 28#64) 16).setWidth 64 <<< 32) = 0 := by
    have hp : (placedField (state.mem.readAt (input.add 26#64) 16) 16) &&& (placedField (state.mem.readAt (input.add 28#64) 16) 32) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 26#64) 16) (state.mem.readAt (input.add 28#64) 16) 16 32 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  have hd173 : (((state.mem.readAt (input.add 26#64) 16).setWidth 64 <<< 16) ||| ((state.mem.readAt (input.add 28#64) 16).setWidth 64 <<< 32)) &&& ((state.mem.readAt (input.add 30#64) 16).setWidth 64 <<< 48) = 0 := by
    have hp : ((placedField (state.mem.readAt (input.add 26#64) 16) 16) ||| (placedField (state.mem.readAt (input.add 28#64) 16) 32)) &&& (placedField (state.mem.readAt (input.add 30#64) 16) 48) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 26#64) 16) (state.mem.readAt (input.add 30#64) 16) 16 48 (by decide)
      have h1_0 := placedField_disjoint (state.mem.readAt (input.add 28#64) 16) (state.mem.readAt (input.add 30#64) 16) 32 48 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, h1_0, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  have hd174 : ((((state.mem.readAt (input.add 26#64) 16).setWidth 64 <<< 16) ||| ((state.mem.readAt (input.add 28#64) 16).setWidth 64 <<< 32)) ||| ((state.mem.readAt (input.add 30#64) 16).setWidth 64 <<< 48)) &&& (((state.mem.readAt (input.add 25#64) 8).setWidth 64 <<< 8) ||| (state.mem.readAt (input.add 24#64) 8).setWidth 64) = 0 := by
    have hp : (((placedField (state.mem.readAt (input.add 26#64) 16) 16) ||| (placedField (state.mem.readAt (input.add 28#64) 16) 32)) ||| (placedField (state.mem.readAt (input.add 30#64) 16) 48)) &&& ((placedField (state.mem.readAt (input.add 25#64) 8) 8) ||| (placedField (state.mem.readAt (input.add 24#64) 8) 0)) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 26#64) 16) (state.mem.readAt (input.add 25#64) 8) 16 8 (by decide)
      have h0_1 := placedField_disjoint (state.mem.readAt (input.add 26#64) 16) (state.mem.readAt (input.add 24#64) 8) 16 0 (by decide)
      have h1_0 := placedField_disjoint (state.mem.readAt (input.add 28#64) 16) (state.mem.readAt (input.add 25#64) 8) 32 8 (by decide)
      have h1_1 := placedField_disjoint (state.mem.readAt (input.add 28#64) 16) (state.mem.readAt (input.add 24#64) 8) 32 0 (by decide)
      have h2_0 := placedField_disjoint (state.mem.readAt (input.add 30#64) 16) (state.mem.readAt (input.add 25#64) 8) 48 8 (by decide)
      have h2_1 := placedField_disjoint (state.mem.readAt (input.add 30#64) 16) (state.mem.readAt (input.add 24#64) 8) 48 0 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, h0_1, h1_0, h1_1, h2_0, h2_1, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    inputChunk3Env, inputChunk3Word,
    hinput, hc2, hc6, hc9, hc13, hc16, hc19, hc20, hc21, hc22, hg24, hg25, hg26, hg28, hg30, hf153, hf156, hf161, hf165, hf170, hs158, hs163, hs167, hs172, hd159, hd168, hd173, hd174, hscratch, hfits,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    placedField, Operation.load, Operation.store, Operation.zext, Operation.or,
    UnOp.compute, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.Verifier.Execution.ScalarWide

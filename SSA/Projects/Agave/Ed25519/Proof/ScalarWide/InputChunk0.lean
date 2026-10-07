import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputFieldFlags
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-! Actual mixed-width loads and assembly of one 64-bit input chunk.
Every shift flag and disjoint OR is proved from its fragment bit intervals. -/

set_option maxRecDepth 100000

namespace Agave.Ed25519.Verifier.Execution.ScalarWide

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

def inputChunk0Env (E : Env program.Γ) (mem : MemoryState) (input : Pointer) : Env program.Γ :=
  let v89 : BitVec 32 := mem.readAt input 32
  let v90 : BitVec 64 := v89.setWidth 64
  let v91 : Pointer := input.add 4#64
  let v92 : BitVec 8 := mem.readAt (input.add 4#64) 8
  let v93 : BitVec 64 := v92.setWidth 64
  let v94 : BitVec 64 := v93 <<< 32
  let v95 : BitVec 64 := v94 ||| v90
  let v96 : Pointer := input.add 5#64
  let v97 : BitVec 8 := mem.readAt (input.add 5#64) 8
  let v98 : BitVec 64 := v97.setWidth 64
  let v99 : BitVec 64 := v98 <<< 40
  let v100 : BitVec 64 := v95 ||| v99
  let v101 : Pointer := input.add 6#64
  let v102 : BitVec 8 := mem.readAt (input.add 6#64) 8
  let v103 : BitVec 64 := v102.setWidth 64
  let v104 : BitVec 64 := v103 <<< 48
  let v105 : BitVec 64 := v100 ||| v104
  let v106 : Pointer := input.add 7#64
  let v107 : BitVec 8 := mem.readAt (input.add 7#64) 8
  let v108 : BitVec 64 := v107.setWidth 64
  let v109 : BitVec 64 := v108 <<< 56
  let v110 : BitVec 64 := v109 ||| v105
  E[%89 := .value v89,
    %90 := .value v90,
    %91 := .value v91,
    %92 := .value v92,
    %93 := .value v93,
    %94 := .value v94,
    %95 := .value v95,
    %96 := .value v96,
    %97 := .value v97,
    %98 := .value v98,
    %99 := .value v99,
    %100 := .value v100,
    %101 := .value v101,
    %102 := .value v102,
    %103 := .value v103,
    %104 := .value v104,
    %105 := .value v105,
    %106 := .value v106,
    %107 := .value v107,
    %108 := .value v108,
    %109 := .value v109,
    %110 := .value v110]

theorem inputChunk0_run (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (input : Pointer)
    (hinput : E.read (%arg1) = .value input)
    (hlive : SmallRange state.mem input 64)
    (hc1 : E.read (%1) = .value 4#64)
    (hc2 : E.read (%2) = .value 32#64)
    (hc3 : E.read (%3) = .value 5#64)
    (hc4 : E.read (%4) = .value 40#64)
    (hc5 : E.read (%5) = .value 6#64)
    (hc6 : E.read (%6) = .value 48#64)
    (hc7 : E.read (%7) = .value 7#64)
    (hc8 : E.read (%8) = .value 56#64)
    : List.foldlM Instr.run E (((program.entry p g).body.drop 89).take 37) state =
      .value (inputChunk0Env E state.mem input,
        state) := by
  change E.args 1 = .value input at hinput
  have hg4 := hlive.gep (k := 4) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (4 : Int)] =
    .value (input.add 4#64) at hg4
  have hg5 := hlive.gep (k := 5) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (5 : Int)] =
    .value (input.add 5#64) at hg5
  have hg6 := hlive.gep (k := 6) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (6 : Int)] =
    .value (input.add 6#64) at hg6
  have hg7 := hlive.gep (k := 7) (by decide)
  change Operation.gepInboundsLive state.mem (.value input) [.value (7 : Int)] =
    .value (input.add 7#64) at hg7
  have hf89 := hlive.fits_add (k := 0) (count := 4) (by decide)
  simp only [Pointer.add_zero] at hf89
  have hf92 := hlive.fits_add (k := 4) (count := 1) (by decide)
  have hf97 := hlive.fits_add (k := 5) (count := 1) (by decide)
  have hf102 := hlive.fits_add (k := 6) (count := 1) (by decide)
  have hf107 := hlive.fits_add (k := 7) (count := 1) (by decide)
  have hs94 := field_shl_nsw_nuw (state.mem.readAt (input.add 4#64) 8) 32 (by decide) (by decide)
  have hs99 := field_shl_nsw_nuw (state.mem.readAt (input.add 5#64) 8) 40 (by decide) (by decide)
  have hs104 := field_shl_nsw_nuw (state.mem.readAt (input.add 6#64) 8) 48 (by decide) (by decide)
  have hs109 := field_shl_nuw (state.mem.readAt (input.add 7#64) 8) 56 (by decide) (by decide)
  have hd95 : ((state.mem.readAt (input.add 4#64) 8).setWidth 64 <<< 32) &&& (state.mem.readAt input 32).setWidth 64 = 0 := by
    have hp : (placedField (state.mem.readAt (input.add 4#64) 8) 32) &&& (placedField (state.mem.readAt input 32) 0) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 4#64) 8) (state.mem.readAt input 32) 32 0 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  have hd100 : (((state.mem.readAt (input.add 4#64) 8).setWidth 64 <<< 32) ||| (state.mem.readAt input 32).setWidth 64) &&& ((state.mem.readAt (input.add 5#64) 8).setWidth 64 <<< 40) = 0 := by
    have hp : ((placedField (state.mem.readAt (input.add 4#64) 8) 32) ||| (placedField (state.mem.readAt input 32) 0)) &&& (placedField (state.mem.readAt (input.add 5#64) 8) 40) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 4#64) 8) (state.mem.readAt (input.add 5#64) 8) 32 40 (by decide)
      have h1_0 := placedField_disjoint (state.mem.readAt input 32) (state.mem.readAt (input.add 5#64) 8) 0 40 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, h1_0, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  have hd105 : ((((state.mem.readAt (input.add 4#64) 8).setWidth 64 <<< 32) ||| (state.mem.readAt input 32).setWidth 64) ||| ((state.mem.readAt (input.add 5#64) 8).setWidth 64 <<< 40)) &&& ((state.mem.readAt (input.add 6#64) 8).setWidth 64 <<< 48) = 0 := by
    have hp : (((placedField (state.mem.readAt (input.add 4#64) 8) 32) ||| (placedField (state.mem.readAt input 32) 0)) ||| (placedField (state.mem.readAt (input.add 5#64) 8) 40)) &&& (placedField (state.mem.readAt (input.add 6#64) 8) 48) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 4#64) 8) (state.mem.readAt (input.add 6#64) 8) 32 48 (by decide)
      have h1_0 := placedField_disjoint (state.mem.readAt input 32) (state.mem.readAt (input.add 6#64) 8) 0 48 (by decide)
      have h2_0 := placedField_disjoint (state.mem.readAt (input.add 5#64) 8) (state.mem.readAt (input.add 6#64) 8) 40 48 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, h1_0, h2_0, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  have hd110 : ((state.mem.readAt (input.add 7#64) 8).setWidth 64 <<< 56) &&& (((((state.mem.readAt (input.add 4#64) 8).setWidth 64 <<< 32) ||| (state.mem.readAt input 32).setWidth 64) ||| ((state.mem.readAt (input.add 5#64) 8).setWidth 64 <<< 40)) ||| ((state.mem.readAt (input.add 6#64) 8).setWidth 64 <<< 48)) = 0 := by
    have hp : (placedField (state.mem.readAt (input.add 7#64) 8) 56) &&& ((((placedField (state.mem.readAt (input.add 4#64) 8) 32) ||| (placedField (state.mem.readAt input 32) 0)) ||| (placedField (state.mem.readAt (input.add 5#64) 8) 40)) ||| (placedField (state.mem.readAt (input.add 6#64) 8) 48)) = 0 := by
      have h0_0 := placedField_disjoint (state.mem.readAt (input.add 7#64) 8) (state.mem.readAt (input.add 4#64) 8) 56 32 (by decide)
      have h0_1 := placedField_disjoint (state.mem.readAt (input.add 7#64) 8) (state.mem.readAt input 32) 56 0 (by decide)
      have h0_2 := placedField_disjoint (state.mem.readAt (input.add 7#64) 8) (state.mem.readAt (input.add 5#64) 8) 56 40 (by decide)
      have h0_3 := placedField_disjoint (state.mem.readAt (input.add 7#64) 8) (state.mem.readAt (input.add 6#64) 8) 56 48 (by decide)
      simp [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
        h0_0, h0_1, h0_2, h0_3, BitVec.zero_or, BitVec.or_zero]
    simpa only [placedField, BitVec.shiftLeft_zero] using hp
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    inputChunk0Env,
    hinput, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hg4, hg5, hg6, hg7, hf89, hf92, hf97, hf102, hf107, hs94, hs99, hs104, hs109, hd95, hd100, hd105, hd110,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    placedField, Operation.load, Operation.store, Operation.zext, Operation.or,
    UnOp.compute, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.Verifier.Execution.ScalarWide

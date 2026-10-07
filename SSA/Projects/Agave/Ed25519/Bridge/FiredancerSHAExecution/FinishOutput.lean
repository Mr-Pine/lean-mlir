import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.FinishPadding
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.Context
import SSA.Projects.Agave.Ed25519.Proof.SHA512.ByteOrder

/-! Exact finalizer output suffix: eight native chaining loads, byte swaps and
output stores. Input/output allocations are separate, preserving unread words. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Verifier.Execution.SHA512Finalization (swapBytes)
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

structure OutputReady (E : Env program.Γ) (context output : Pointer) : Prop where
  contextReg : E.read (%arg0) = .value context
  outputReg : E.read (%arg1) = .value output
  chain : E.read (%25) = .value (context.add 128#64)
  c11 : E.read (%11) = .value 136#64
  c12 : E.read (%12) = .value 8#64
  c13 : E.read (%13) = .value 144#64
  c14 : E.read (%14) = .value 16#64
  c15 : E.read (%15) = .value 152#64
  c16 : E.read (%16) = .value 24#64
  c17 : E.read (%17) = .value 160#64
  c18 : E.read (%18) = .value 32#64
  c19 : E.read (%19) = .value 168#64
  c20 : E.read (%20) = .value 40#64
  c21 : E.read (%21) = .value 176#64
  c22 : E.read (%22) = .value 48#64
  c23 : E.read (%23) = .value 184#64
  c24 : E.read (%24) = .value 56#64

def outputMemory (m : MemoryState) (output : Pointer) (s : State) : MemoryState :=
  let m := m.storeAt output (swapBytes s.a)
  let m := m.storeAt (output.add 8#64) (swapBytes s.b)
  let m := m.storeAt (output.add 16#64) (swapBytes s.c)
  let m := m.storeAt (output.add 24#64) (swapBytes s.d)
  let m := m.storeAt (output.add 32#64) (swapBytes s.e)
  let m := m.storeAt (output.add 40#64) (swapBytes s.f)
  let m := m.storeAt (output.add 48#64) (swapBytes s.g)
  let m := m.storeAt (output.add 56#64) (swapBytes s.h)
  m

def outputEnv (E : Env program.Γ) (context output : Pointer) (s : State) : Env program.Γ :=
  E[%44 := .value (s.a),
    %45 := .value (swapBytes s.a),
    %46 := .value (context.add 136#64),
    %47 := .value (s.b),
    %48 := .value (swapBytes s.b),
    %49 := .value (output.add 8#64),
    %50 := .value (context.add 144#64),
    %51 := .value (s.c),
    %52 := .value (swapBytes s.c),
    %53 := .value (output.add 16#64),
    %54 := .value (context.add 152#64),
    %55 := .value (s.d),
    %56 := .value (swapBytes s.d),
    %57 := .value (output.add 24#64),
    %58 := .value (context.add 160#64),
    %59 := .value (s.e),
    %60 := .value (swapBytes s.e),
    %61 := .value (output.add 32#64),
    %62 := .value (context.add 168#64),
    %63 := .value (s.f),
    %64 := .value (swapBytes s.f),
    %65 := .value (output.add 40#64),
    %66 := .value (context.add 176#64),
    %67 := .value (s.g),
    %68 := .value (swapBytes s.g),
    %69 := .value (output.add 48#64),
    %70 := .value (context.add 184#64),
    %71 := .value (s.h),
    %72 := .value (swapBytes s.h),
    %73 := .value (output.add 56#64)]

theorem output_body (core : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (E : Env program.Γ) (state : GlobalState) (context output : Pointer) (s : State)
    (h : OutputReady E context output) (hc : SmallRange state.mem context 224)
    (ho : SmallRange state.mem output 64) (hne : output.id ≠ context.id)
    (hchain : readState state.mem context = s) :
    List.foldlM Instr.run E ((program.bb2 core).body.drop 10) state =
      .value (outputEnv E context output s, {state with mem := outputMemory state.mem output s}) := by
  have harg0 : E.args 0 = .value context := h.contextReg
  have harg1 : E.args 1 = .value output := h.outputReg
  have hread0 : state.mem.readAt (context.add 128#64) 64 = s.a := congrArg State.a hchain
  have hread1 : state.mem.readAt (context.add 136#64) 64 = s.b := congrArg State.b hchain
  have hread2 : state.mem.readAt (context.add 144#64) 64 = s.c := congrArg State.c hchain
  have hread3 : state.mem.readAt (context.add 152#64) 64 = s.d := congrArg State.d hchain
  have hread4 : state.mem.readAt (context.add 160#64) 64 = s.e := congrArg State.e hchain
  have hread5 : state.mem.readAt (context.add 168#64) 64 = s.f := congrArg State.f hchain
  have hread6 : state.mem.readAt (context.add 176#64) 64 = s.g := congrArg State.g hchain
  have hread7 : state.mem.readAt (context.add 184#64) 64 = s.h := congrArg State.h hchain
  have hc0 := hc
  have ho0 := ho
  have hc1 := hc0.storeAt output (swapBytes s.a)
  have ho1 := ho0.storeAt output (swapBytes s.a)
  have hf0 := hc0.fits_add (k := 128) (count := 8) (by decide)
  have hfo0 := ho0.fits_add (k := 0) (count := 8) (by decide)
  have hc2 := hc1.storeAt (output.add 8#64) (swapBytes s.b)
  have ho2 := ho1.storeAt (output.add 8#64) (swapBytes s.b)
  have hf1 := hc1.fits_add (k := 136) (count := 8) (by decide)
  have hfo1 := ho1.fits_add (k := 8) (count := 8) (by decide)
  have hgc1 := hc1.gep (k := 136) (by decide)
  have hgo1 := ho1.gep (k := 8) (by decide)
  have hc3 := hc2.storeAt (output.add 16#64) (swapBytes s.c)
  have ho3 := ho2.storeAt (output.add 16#64) (swapBytes s.c)
  have hf2 := hc2.fits_add (k := 144) (count := 8) (by decide)
  have hfo2 := ho2.fits_add (k := 16) (count := 8) (by decide)
  have hgc2 := hc2.gep (k := 144) (by decide)
  have hgo2 := ho2.gep (k := 16) (by decide)
  have hc4 := hc3.storeAt (output.add 24#64) (swapBytes s.d)
  have ho4 := ho3.storeAt (output.add 24#64) (swapBytes s.d)
  have hf3 := hc3.fits_add (k := 152) (count := 8) (by decide)
  have hfo3 := ho3.fits_add (k := 24) (count := 8) (by decide)
  have hgc3 := hc3.gep (k := 152) (by decide)
  have hgo3 := ho3.gep (k := 24) (by decide)
  have hc5 := hc4.storeAt (output.add 32#64) (swapBytes s.e)
  have ho5 := ho4.storeAt (output.add 32#64) (swapBytes s.e)
  have hf4 := hc4.fits_add (k := 160) (count := 8) (by decide)
  have hfo4 := ho4.fits_add (k := 32) (count := 8) (by decide)
  have hgc4 := hc4.gep (k := 160) (by decide)
  have hgo4 := ho4.gep (k := 32) (by decide)
  have hc6 := hc5.storeAt (output.add 40#64) (swapBytes s.f)
  have ho6 := ho5.storeAt (output.add 40#64) (swapBytes s.f)
  have hf5 := hc5.fits_add (k := 168) (count := 8) (by decide)
  have hfo5 := ho5.fits_add (k := 40) (count := 8) (by decide)
  have hgc5 := hc5.gep (k := 168) (by decide)
  have hgo5 := ho5.gep (k := 40) (by decide)
  have hc7 := hc6.storeAt (output.add 48#64) (swapBytes s.g)
  have ho7 := ho6.storeAt (output.add 48#64) (swapBytes s.g)
  have hf6 := hc6.fits_add (k := 176) (count := 8) (by decide)
  have hfo6 := ho6.fits_add (k := 48) (count := 8) (by decide)
  have hgc6 := hc6.gep (k := 176) (by decide)
  have hgo6 := ho6.gep (k := 48) (by decide)
  have hc8 := hc7.storeAt (output.add 56#64) (swapBytes s.h)
  have ho8 := ho7.storeAt (output.add 56#64) (swapBytes s.h)
  have hf7 := hc7.fits_add (k := 184) (count := 8) (by decide)
  have hfo7 := ho7.fits_add (k := 56) (count := 8) (by decide)
  have hgc7 := hc7.gep (k := 184) (by decide)
  have hgo7 := ho7.gep (k := 56) (by decide)
  have hd01 : (Range.of output 64).Disjoint (Range.of (context.add 136#64) 64) := Or.inl hne
  have hd02 : (Range.of output 64).Disjoint (Range.of (context.add 144#64) 64) := Or.inl hne
  have hd12 : (Range.of (output.add 8#64) 64).Disjoint (Range.of (context.add 144#64) 64) := Or.inl hne
  have hd03 : (Range.of output 64).Disjoint (Range.of (context.add 152#64) 64) := Or.inl hne
  have hd13 : (Range.of (output.add 8#64) 64).Disjoint (Range.of (context.add 152#64) 64) := Or.inl hne
  have hd23 : (Range.of (output.add 16#64) 64).Disjoint (Range.of (context.add 152#64) 64) := Or.inl hne
  have hd04 : (Range.of output 64).Disjoint (Range.of (context.add 160#64) 64) := Or.inl hne
  have hd14 : (Range.of (output.add 8#64) 64).Disjoint (Range.of (context.add 160#64) 64) := Or.inl hne
  have hd24 : (Range.of (output.add 16#64) 64).Disjoint (Range.of (context.add 160#64) 64) := Or.inl hne
  have hd34 : (Range.of (output.add 24#64) 64).Disjoint (Range.of (context.add 160#64) 64) := Or.inl hne
  have hd05 : (Range.of output 64).Disjoint (Range.of (context.add 168#64) 64) := Or.inl hne
  have hd15 : (Range.of (output.add 8#64) 64).Disjoint (Range.of (context.add 168#64) 64) := Or.inl hne
  have hd25 : (Range.of (output.add 16#64) 64).Disjoint (Range.of (context.add 168#64) 64) := Or.inl hne
  have hd35 : (Range.of (output.add 24#64) 64).Disjoint (Range.of (context.add 168#64) 64) := Or.inl hne
  have hd45 : (Range.of (output.add 32#64) 64).Disjoint (Range.of (context.add 168#64) 64) := Or.inl hne
  have hd06 : (Range.of output 64).Disjoint (Range.of (context.add 176#64) 64) := Or.inl hne
  have hd16 : (Range.of (output.add 8#64) 64).Disjoint (Range.of (context.add 176#64) 64) := Or.inl hne
  have hd26 : (Range.of (output.add 16#64) 64).Disjoint (Range.of (context.add 176#64) 64) := Or.inl hne
  have hd36 : (Range.of (output.add 24#64) 64).Disjoint (Range.of (context.add 176#64) 64) := Or.inl hne
  have hd46 : (Range.of (output.add 32#64) 64).Disjoint (Range.of (context.add 176#64) 64) := Or.inl hne
  have hd56 : (Range.of (output.add 40#64) 64).Disjoint (Range.of (context.add 176#64) 64) := Or.inl hne
  have hd07 : (Range.of output 64).Disjoint (Range.of (context.add 184#64) 64) := Or.inl hne
  have hd17 : (Range.of (output.add 8#64) 64).Disjoint (Range.of (context.add 184#64) 64) := Or.inl hne
  have hd27 : (Range.of (output.add 16#64) 64).Disjoint (Range.of (context.add 184#64) 64) := Or.inl hne
  have hd37 : (Range.of (output.add 24#64) 64).Disjoint (Range.of (context.add 184#64) 64) := Or.inl hne
  have hd47 : (Range.of (output.add 32#64) 64).Disjoint (Range.of (context.add 184#64) 64) := Or.inl hne
  have hd57 : (Range.of (output.add 40#64) 64).Disjoint (Range.of (context.add 184#64) 64) := Or.inl hne
  have hd67 : (Range.of (output.add 48#64) 64).Disjoint (Range.of (context.add 184#64) 64) := Or.inl hne
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at hgc1 hgo1 hgc2 hgo2 hgc3 hgo3 hgc4 hgo4 hgc5 hgo5 hgc6 hgo6 hgc7 hgo7 hfo0
  have hswap (word : Word) : Operation.bswap (.value word) = .value (swapBytes word) := rfl
  simp [program.bb2, List.foldlM_cons, List.foldlM_nil, Instr.run,
    outputEnv, outputMemory, harg0, harg1, h.chain,
    h.c11, h.c12, h.c13, h.c14, h.c15, h.c16, h.c17, h.c18, h.c19, h.c20, h.c21, h.c22, h.c23, h.c24,
    hread0, hf0, hfo0, hread1, hf1, hfo1, hread2, hf2, hfo2, hread3, hf3, hfo3, hread4, hf4, hfo4, hread5, hf5, hfo5, hread6, hf6, hfo6, hread7, hf7, hfo7,
    hgc1, hgo1, hgc2, hgo2, hgc3, hgo3, hgc4, hgo4, hgc5, hgo5, hgc6, hgo6, hgc7, hgo7,
    MemoryState.readAt_storeAt_disjoint hd01, MemoryState.readAt_storeAt_disjoint hd02, MemoryState.readAt_storeAt_disjoint hd12, MemoryState.readAt_storeAt_disjoint hd03, MemoryState.readAt_storeAt_disjoint hd13, MemoryState.readAt_storeAt_disjoint hd23, MemoryState.readAt_storeAt_disjoint hd04, MemoryState.readAt_storeAt_disjoint hd14, MemoryState.readAt_storeAt_disjoint hd24, MemoryState.readAt_storeAt_disjoint hd34, MemoryState.readAt_storeAt_disjoint hd05, MemoryState.readAt_storeAt_disjoint hd15, MemoryState.readAt_storeAt_disjoint hd25, MemoryState.readAt_storeAt_disjoint hd35, MemoryState.readAt_storeAt_disjoint hd45, MemoryState.readAt_storeAt_disjoint hd06, MemoryState.readAt_storeAt_disjoint hd16, MemoryState.readAt_storeAt_disjoint hd26, MemoryState.readAt_storeAt_disjoint hd36, MemoryState.readAt_storeAt_disjoint hd46, MemoryState.readAt_storeAt_disjoint hd56, MemoryState.readAt_storeAt_disjoint hd07, MemoryState.readAt_storeAt_disjoint hd17, MemoryState.readAt_storeAt_disjoint hd27, MemoryState.readAt_storeAt_disjoint hd37, MemoryState.readAt_storeAt_disjoint hd47, MemoryState.readAt_storeAt_disjoint hd57, MemoryState.readAt_storeAt_disjoint hd67,
    Operation.load, Operation.store, hswap,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    UnOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish

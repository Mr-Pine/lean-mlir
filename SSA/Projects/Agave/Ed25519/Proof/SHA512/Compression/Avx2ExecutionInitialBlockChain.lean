import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairReady
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionFeedForward

namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

structure InitialChainReady (E : Env program.Γ) (chain : Pointer) : Prop where
  ptr : E.read (%arg0) = .value chain
  c8 : E.read (%3) = .value 8#64
  c16 : E.read (%4) = .value 16#64
  c24 : E.read (%5) = .value 24#64
  c32 : E.read (%6) = .value 32#64
  c40 : E.read (%7) = .value 40#64
  c48 : E.read (%8) = .value 48#64
  c56 : E.read (%9) = .value 56#64

structure InitialChainReads (m : MemoryState) (chain : Pointer) (s : Spec.State) : Prop where
  a : m.readAt chain 64 = s.a
  b : m.readAt (chain.add 8#64) 64 = s.b
  c : m.readAt (chain.add 16#64) 64 = s.c
  d : m.readAt (chain.add 24#64) 64 = s.d
  e : m.readAt (chain.add 32#64) 64 = s.e
  f : m.readAt (chain.add 40#64) 64 = s.f
  g : m.readAt (chain.add 48#64) 64 = s.g
  h : m.readAt (chain.add 56#64) 64 = s.h

/-- The eight concrete chain reads decode the public native chaining ABI. -/
theorem initialChainReads_unpack (mem : MemoryState) (chain : Pointer)
    (hc : SmallRange mem chain 64) :
    InitialChainReads mem chain (Spec.unpack (mem.readAt chain 512)) := by
  constructor
  · have hr := MemoryState.readAt_add_of_readAt (off := 0#64) (w := 64)
      hc.fits (hc.no_wrap (k := 0) (by decide)) (by decide) rfl
    simpa [Spec.unpack] using hr
  · have hr := MemoryState.readAt_add_of_readAt (off := 8#64) (w := 64)
      hc.fits (hc.no_wrap (k := 8) (by decide)) (by decide) rfl
    simpa [Spec.unpack] using hr
  · have hr := MemoryState.readAt_add_of_readAt (off := 16#64) (w := 64)
      hc.fits (hc.no_wrap (k := 16) (by decide)) (by decide) rfl
    simpa [Spec.unpack] using hr
  · have hr := MemoryState.readAt_add_of_readAt (off := 24#64) (w := 64)
      hc.fits (hc.no_wrap (k := 24) (by decide)) (by decide) rfl
    simpa [Spec.unpack] using hr
  · have hr := MemoryState.readAt_add_of_readAt (off := 32#64) (w := 64)
      hc.fits (hc.no_wrap (k := 32) (by decide)) (by decide) rfl
    simpa [Spec.unpack] using hr
  · have hr := MemoryState.readAt_add_of_readAt (off := 40#64) (w := 64)
      hc.fits (hc.no_wrap (k := 40) (by decide)) (by decide) rfl
    simpa [Spec.unpack] using hr
  · have hr := MemoryState.readAt_add_of_readAt (off := 48#64) (w := 64)
      hc.fits (hc.no_wrap (k := 48) (by decide)) (by decide) rfl
    simpa [Spec.unpack] using hr
  · have hr := MemoryState.readAt_add_of_readAt (off := 56#64) (w := 64)
      hc.fits (hc.no_wrap (k := 56) (by decide)) (by decide) rfl
    simpa [Spec.unpack] using hr

def initialChainEnv (E : Env program.Γ) (chain : Pointer) (s : Spec.State) : Env program.Γ :=
  E[%92 := .value s.a, %93 := .value (chain.add 8#64),
    %94 := .value s.b, %95 := .value (chain.add 16#64),
    %96 := .value s.c, %97 := .value (chain.add 24#64),
    %98 := .value s.d, %99 := .value (chain.add 32#64),
    %100 := .value s.e, %101 := .value (chain.add 40#64),
    %102 := .value s.f, %103 := .value (chain.add 48#64),
    %104 := .value s.g, %105 := .value (chain.add 56#64), %106 := .value s.h]

theorem initialChainEnv_frame (E : Env program.Γ) (chain : Pointer) (s : Spec.State) :
    RegFrame 92 106 E (initialChainEnv E chain s) := by
  unfold initialChainEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

/-- The exact first eighteen instructions of bb2, including both scope declarations. -/
theorem initial_chain_body (E : Env program.Γ) (mem : GlobalState)
    (chain : Pointer) (s : Spec.State) (h : InitialChainReady E chain)
    (hc : SmallRange mem.mem chain 64) (hr : InitialChainReads mem.mem chain s) :
    List.foldlM Instr.run E (program.bb2.body.take 18) mem =
      .value (initialChainEnv E chain s, mem) := by
  have hptr : E.args 0 = .value chain := h.ptr
  have hg8 := hc.gep (k := 8) (by decide)
  have hg16 := hc.gep (k := 16) (by decide)
  have hg24 := hc.gep (k := 24) (by decide)
  have hg32 := hc.gep (k := 32) (by decide)
  have hg40 := hc.gep (k := 40) (by decide)
  have hg48 := hc.gep (k := 48) (by decide)
  have hg56 := hc.gep (k := 56) (by decide)
  norm_num only at hg8 hg16 hg24 hg32 hg40 hg48 hg56
  have hf0 : Fits mem.mem chain 64 := by
    simpa only [Pointer.add_zero] using hc.fits_add (k := 0) (count := 8) (by decide)
  have hf8 := hc.fits_add (k := 8) (count := 8) (by decide)
  have hf16 := hc.fits_add (k := 16) (count := 8) (by decide)
  have hf24 := hc.fits_add (k := 24) (count := 8) (by decide)
  have hf32 := hc.fits_add (k := 32) (count := 8) (by decide)
  have hf40 := hc.fits_add (k := 40) (count := 8) (by decide)
  have hf48 := hc.fits_add (k := 48) (count := 8) (by decide)
  have hf56 := hc.fits_add (k := 56) (count := 8) (by decide)
  simp [program.bb2, List.foldlM_cons, List.foldlM_nil, Instr.run,
    initialChainEnv, hptr, h.c8, h.c16, h.c24, h.c32, h.c40, h.c48, h.c56,
    hg8, hg16, hg24, hg32, hg40, hg48, hg56,
    hf0, hf8, hf16, hf24, hf32, hf40, hf48, hf56,
    hr.a, hr.b, hr.c, hr.d, hr.e, hr.f, hr.g, hr.h,
    GepIndex.inboundsOffset, Operation.load,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

/-- The exact simultaneous bb2-to-bb4 assignment. -/
def initialGroupEnv (E : Env program.Γ) : Env program.Γ :=
  E[%155 := E.read (%4), %156 := E.read (%23),
    %157 := E.read (%114), %158 := E.read (%109),
    %159 := E.read (%138), %160 := E.read (%132),
    %161 := E.read (%150), %162 := E.read (%120),
    %163 := E.read (%126), %164 := E.read (%144),
    %165 := E.read (%106), %166 := E.read (%100),
    %167 := E.read (%104), %168 := E.read (%102),
    %169 := E.read (%92), %170 := E.read (%94),
    %171 := E.read (%96), %172 := E.read (%98)]

theorem initial_group_exit (E : Env program.Γ) (mem : GlobalState) :
    program.bb2.exit.run program.blockParams E mem =
      .value ((initialGroupEnv E, .inr 4), mem) := by
  simp [program.bb2, Exit.run, Jump.run, initialGroupEnv,
    Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    EffectM.pure_eq, mlir_env, mlir_effect]

end Agave.Ed25519.SHA512.Execution.Avx2

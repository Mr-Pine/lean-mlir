import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.DispatchExecutionControl

/-! Exact count-one scalar CFG prefix. The imported dispatcher inlines the
scalar backend into bb4. This module reaches that real block, decoding all
eight incoming chaining words and establishing its cursor/end relationship.
The eighty-round body remains a separate arithmetic execution obligation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000

namespace Agave.Ed25519.SHA512.Execution.Dispatch
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution

/-- Scalar slice extent and the nonzero-count test, as emitted in bb2. -/
def scalarBoundsEnv (E : Env program.Γ) (data : Pointer) : Env program.Γ :=
  E[%175 := .value 128#64, %176 := .value (data.add 128#64), %177 := .value 0#1]

/-- Count one discharges both shift overflow flags and the nonzero test.
The complete block range discharges the end pointer's inbounds flags. -/
theorem scalar_one_bounds_step (E : Env program.Γ) (state : GlobalState)
    (data : Pointer) (hd : SmallRange state.mem data 128)
    (hdata : E.read (%arg1) = .value data)
    (hcount : E.read (%arg2) = .value 1#64)
    (hseven : E.read (%1) = .value 7#64)
    (hzero : E.read (%2) = .value 0#64) :
    program.bb2.run program.blockParams E state =
      .value ((scalarBoundsEnv E data, .inr 3), state) := by
  change E.args 1 = .value data at hdata
  change E.args 2 = .value 1#64 at hcount
  have hidx : Operation.gepInboundsIndex 1 (.value 128#64) = .value (128 : Int) := by decide
  have hg := hd.gep (k := 128) (by decide)
  change Operation.gepInboundsLive state.mem (.value data) [.value (128 : Int)] = .value (data.add 128#64) at hg
  simp [BasicBlock.run, program.bb2, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Exit.run, Jump.run, scalarBoundsEnv, hdata, hcount, hseven, hzero,
    Operation.shl, Operation.icmp, GepIndex.inboundsOffset, hg, hidx,
    BinOp.compute, mlir_env, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect]

/-- Native little-endian words of the chaining-state ABI. -/
def scalarChainState (mem : MemoryState) (chain : Pointer) : Spec.State :=
  ⟨mem.readAt chain 64, mem.readAt (chain.add 8#64) 64,
    mem.readAt (chain.add 16#64) 64, mem.readAt (chain.add 24#64) 64,
    mem.readAt (chain.add 32#64) 64, mem.readAt (chain.add 40#64) 64,
    mem.readAt (chain.add 48#64) 64, mem.readAt (chain.add 56#64) 64⟩

/-- The scalar loads interpret the public 512-bit ABI exactly as the
independent specification's eight-word unpacking. -/
theorem scalarChainState_eq_unpack (mem : MemoryState) (chain : Pointer)
    (hc : SmallRange mem chain 64) :
    scalarChainState mem chain = Spec.unpack (mem.readAt chain 512) := by
  have hr0 := MemoryState.readAt_add_of_readAt (off := 0#64) (w := 64)
    hc.fits (hc.no_wrap (k := 0) (by decide)) (by decide) rfl
  have hr8 := MemoryState.readAt_add_of_readAt (off := 8#64) (w := 64)
    hc.fits (hc.no_wrap (k := 8) (by decide)) (by decide) rfl
  have hr16 := MemoryState.readAt_add_of_readAt (off := 16#64) (w := 64)
    hc.fits (hc.no_wrap (k := 16) (by decide)) (by decide) rfl
  have hr24 := MemoryState.readAt_add_of_readAt (off := 24#64) (w := 64)
    hc.fits (hc.no_wrap (k := 24) (by decide)) (by decide) rfl
  have hr32 := MemoryState.readAt_add_of_readAt (off := 32#64) (w := 64)
    hc.fits (hc.no_wrap (k := 32) (by decide)) (by decide) rfl
  have hr40 := MemoryState.readAt_add_of_readAt (off := 40#64) (w := 64)
    hc.fits (hc.no_wrap (k := 40) (by decide)) (by decide) rfl
  have hr48 := MemoryState.readAt_add_of_readAt (off := 48#64) (w := 64)
    hc.fits (hc.no_wrap (k := 48) (by decide)) (by decide) rfl
  have hr56 := MemoryState.readAt_add_of_readAt (off := 56#64) (w := 64)
    hc.fits (hc.no_wrap (k := 56) (by decide)) (by decide) rfl
  simp only [Pointer.add_zero] at hr0
  unfold scalarChainState Spec.unpack
  rw [hr0, hr8, hr16, hr24, hr32, hr40, hr48, hr56]
  rfl

/-- The eight emitted chain loads and seven chain-address computations. -/
def scalarLoadEnv (E : Env program.Γ) (chain : Pointer) (s : Spec.State) :
    Env program.Γ :=
  E[%178 := .value s.a, %179 := .value (chain.add 8#64),
    %180 := .value (chain.add 16#64), %181 := .value (chain.add 24#64),
    %182 := .value (chain.add 32#64), %183 := .value (chain.add 40#64),
    %184 := .value (chain.add 48#64), %185 := .value (chain.add 56#64),
    %186 := .value s.b, %187 := .value s.c, %188 := .value s.d,
    %189 := .value s.e, %190 := .value s.f, %191 := .value s.g,
    %192 := .value s.h]

/-- Actual bb4 block parameters, in the original compiler order. -/
def scalarLoopEnv (E : Env program.Γ) (data : Pointer) (s : Spec.State) :
    Env program.Γ :=
  E[%193 := .value s.h, %194 := .value s.g, %195 := .value s.f,
    %196 := .value s.e, %197 := .value s.d, %198 := .value s.c,
    %199 := .value s.b, %200 := .value data, %201 := .value s.a]

/-- Successful read-only execution of the emitted scalar chain loads. -/
theorem scalar_load_body (E : Env program.Γ) (state : GlobalState)
    (chain : Pointer) (hc : SmallRange state.mem chain 64)
    (hchain : E.read (%arg0) = .value chain) :
    List.foldlM Instr.run E program.bb3.body state =
      .value (scalarLoadEnv E chain (scalarChainState state.mem chain), state) := by
  change E.args 0 = .value chain at hchain
  have hf0 := hc.fits_add (k := 0) (count := 8) (by decide)
  simp only [Pointer.add_zero] at hf0
  have hf8 := hc.fits_add (k := 8) (count := 8) (by decide)
  have hf16 := hc.fits_add (k := 16) (count := 8) (by decide)
  have hf24 := hc.fits_add (k := 24) (count := 8) (by decide)
  have hf32 := hc.fits_add (k := 32) (count := 8) (by decide)
  have hf40 := hc.fits_add (k := 40) (count := 8) (by decide)
  have hf48 := hc.fits_add (k := 48) (count := 8) (by decide)
  have hf56 := hc.fits_add (k := 56) (count := 8) (by decide)
  have hg8 := hc.gep (k := 8) (by decide)
  change Operation.gepInboundsLive state.mem (.value chain) [.value (8 : Int)] = .value (chain.add 8#64) at hg8
  have hg16 := hc.gep (k := 16) (by decide)
  change Operation.gepInboundsLive state.mem (.value chain) [.value (16 : Int)] = .value (chain.add 16#64) at hg16
  have hg24 := hc.gep (k := 24) (by decide)
  change Operation.gepInboundsLive state.mem (.value chain) [.value (24 : Int)] = .value (chain.add 24#64) at hg24
  have hg32 := hc.gep (k := 32) (by decide)
  change Operation.gepInboundsLive state.mem (.value chain) [.value (32 : Int)] = .value (chain.add 32#64) at hg32
  have hg40 := hc.gep (k := 40) (by decide)
  change Operation.gepInboundsLive state.mem (.value chain) [.value (40 : Int)] = .value (chain.add 40#64) at hg40
  have hg48 := hc.gep (k := 48) (by decide)
  change Operation.gepInboundsLive state.mem (.value chain) [.value (48 : Int)] = .value (chain.add 48#64) at hg48
  have hg56 := hc.gep (k := 56) (by decide)
  change Operation.gepInboundsLive state.mem (.value chain) [.value (56 : Int)] = .value (chain.add 56#64) at hg56
  simp [program.bb3, List.foldlM_cons, List.foldlM_nil, Instr.run,
    scalarLoadEnv, scalarChainState, hchain,
    hf0, hf8, hf16, hf24, hf32, hf40, hf48, hf56,
    hg8, hg16, hg24, hg32, hg40, hg48, hg56,
    GepIndex.inboundsOffset, Operation.load,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

@[simp] theorem dispatch_params4 : program.blockParams 4 =
    .cons (%193) (.cons (%194) (.cons (%195) (.cons (%196) (.cons (%197)
      (.cons (%198) (.cons (%199) (.cons (%200) (.cons (%201) .nil)))))))) := rfl

/-- The actual branch assigns all nine scalar-body parameters. -/
theorem scalar_load_step (E : Env program.Γ) (state : GlobalState)
    (chain data : Pointer) (hc : SmallRange state.mem chain 64)
    (hchain : E.read (%arg0) = .value chain)
    (hdata : E.read (%arg1) = .value data) :
    program.bb3.run program.blockParams E state =
      .value ((scalarLoopEnv
        (scalarLoadEnv E chain (scalarChainState state.mem chain))
        data (scalarChainState state.mem chain), .inr 4), state) := by
  rw [BasicBlock.run_eq]
  change (List.foldlM Instr.run E program.bb3.body state >>= _) = _
  rw [scalar_load_body E state chain hc hchain]
  change E.args 1 = .value data at hdata
  simp [program.bb3, Exit.run, Jump.run, scalarLoopEnv, scalarLoadEnv,
    hdata, mlir_env, EffectM.bind_eq, EffectM.pure_eq]

end Agave.Ed25519.SHA512.Execution.Dispatch

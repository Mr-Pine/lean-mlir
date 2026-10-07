import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreOuter
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Frame

/-! Exact imported core entry: one private ring allocation, the live inbounds
chaining-state addresses, eight native loads, and transfer to the outer loop. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Verifier.Execution.SHA512Finalization
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

structure ChainMemory (m : MemoryState) (p : Pointer) (s : State) : Prop where
  a : m.readAt p 64 = s.a
  b : m.readAt (p.add 8#64) 64 = s.b
  c : m.readAt (p.add 16#64) 64 = s.c
  d : m.readAt (p.add 24#64) 64 = s.d
  e : m.readAt (p.add 32#64) 64 = s.e
  f : m.readAt (p.add 40#64) 64 = s.f
  g : m.readAt (p.add 48#64) 64 = s.g
  h : m.readAt (p.add 56#64) 64 = s.h

def entryConstants (E : Env program.Γ) (kp : Pointer) : Env program.Γ :=
  E[%0 := .value 1#32,
    %1 := .value 8#64,
    %2 := .value 16#64,
    %3 := .value 24#64,
    %4 := .value 32#64,
    %5 := .value 40#64,
    %6 := .value 48#64,
    %7 := .value 56#64,
    %8 := .value 0#64,
    %9 := .value 3#64,
    %10 := .value 50#64,
    %11 := .value 46#64,
    %12 := .value 23#64,
    %13 := .value 18446744073709551615#64,
    %14 := .value kp,
    %15 := .value 36#64,
    %16 := .value 30#64,
    %17 := .value 25#64,
    %18 := .value 1#64,
    %19 := .value 15#64,
    %20 := .value 14#64,
    %21 := .value 63#64,
    %22 := .value 7#64,
    %23 := .value 45#64,
    %24 := .value 6#64,
    %25 := .value 9#64,
    %26 := .value 80#64,
    %27 := .value 128#64]

def coreEntryEnv (E : Env program.Γ) (kp chain stack : Pointer) (s : State) : Env program.Γ :=
  (entryConstants E kp)[%28 := .value stack,
    %29 := .value (chain.add 8#64),
    %30 := .value (chain.add 16#64),
    %31 := .value (chain.add 24#64),
    %32 := .value (chain.add 32#64),
    %33 := .value (chain.add 40#64),
    %34 := .value (chain.add 48#64),
    %35 := .value (chain.add 56#64),
    %36 := .value s.a,
    %37 := .value s.b,
    %38 := .value s.c,
    %39 := .value s.d,
    %40 := .value s.e,
    %41 := .value s.f,
    %42 := .value s.g,
    %43 := .value s.h]

theorem coreEntry_live (state : GlobalState) (hwf : state.WF) :
    SmallRange (state.alloca 128).mem state.allocaPtr 128 :=
  allocateSlots_slot_live [128] hwf (i := 0) (by decide) (by decide)

theorem coreEntry_frame (state : GlobalState) (hwf : state.WF) :
    (state.alloca 128).mem.eraseFrom state.alloc.nextFreeBlock = state.mem :=
  allocateSlots_frame [128] state hwf

private theorem modifyGet_apply (f : GlobalState → α × GlobalState) (s : GlobalState) :
    (modifyGet f : EffectM α) s = .value (f s) := rfl

theorem coreEntry_body (E : Env program.Γ) (state : GlobalState)
    (kp chain : Pointer) (s : State) (hwf : state.WF)
    (hp : E.read (%arg0) = .value chain) (hc : SmallRange state.mem chain 64)
    (hm : ChainMemory state.mem chain s) :
    List.foldlM Instr.run E (program.bb0 kp).body state =
      .value (coreEntryEnv E kp chain state.allocaPtr s, state.alloca 128) := by
  have hp0 : E.args 0 = .value chain := hp
  have hc' : SmallRange (state.alloca 128).mem chain 64 := smallRange_alloca hwf hc
  have hf0 : Fits (state.alloca 128).mem chain 64 := by
    simpa using hc'.fits_add (k := 0) (count := 8) (by decide)
  have hr0 : (state.alloca 128).mem.readAt chain 64 = s.a :=
    (MemoryState.readAt_alloca hwf hc.fits).trans hm.a
  have hg1 := hc'.gep (k := 8) (by decide)
  have hf1 := hc'.fits_add (k := 8) (count := 8) (by decide)
  have hr1 : (state.alloca 128).mem.readAt (chain.add 8#64) 64 = s.b :=
    (MemoryState.readAt_alloca hwf (hc.fits_add (k := 8) (count := 8) (by decide))).trans hm.b
  have hg2 := hc'.gep (k := 16) (by decide)
  have hf2 := hc'.fits_add (k := 16) (count := 8) (by decide)
  have hr2 : (state.alloca 128).mem.readAt (chain.add 16#64) 64 = s.c :=
    (MemoryState.readAt_alloca hwf (hc.fits_add (k := 16) (count := 8) (by decide))).trans hm.c
  have hg3 := hc'.gep (k := 24) (by decide)
  have hf3 := hc'.fits_add (k := 24) (count := 8) (by decide)
  have hr3 : (state.alloca 128).mem.readAt (chain.add 24#64) 64 = s.d :=
    (MemoryState.readAt_alloca hwf (hc.fits_add (k := 24) (count := 8) (by decide))).trans hm.d
  have hg4 := hc'.gep (k := 32) (by decide)
  have hf4 := hc'.fits_add (k := 32) (count := 8) (by decide)
  have hr4 : (state.alloca 128).mem.readAt (chain.add 32#64) 64 = s.e :=
    (MemoryState.readAt_alloca hwf (hc.fits_add (k := 32) (count := 8) (by decide))).trans hm.e
  have hg5 := hc'.gep (k := 40) (by decide)
  have hf5 := hc'.fits_add (k := 40) (count := 8) (by decide)
  have hr5 : (state.alloca 128).mem.readAt (chain.add 40#64) 64 = s.f :=
    (MemoryState.readAt_alloca hwf (hc.fits_add (k := 40) (count := 8) (by decide))).trans hm.f
  have hg6 := hc'.gep (k := 48) (by decide)
  have hf6 := hc'.fits_add (k := 48) (count := 8) (by decide)
  have hr6 : (state.alloca 128).mem.readAt (chain.add 48#64) 64 = s.g :=
    (MemoryState.readAt_alloca hwf (hc.fits_add (k := 48) (count := 8) (by decide))).trans hm.g
  have hg7 := hc'.gep (k := 56) (by decide)
  have hf7 := hc'.fits_add (k := 56) (count := 8) (by decide)
  have hr7 : (state.alloca 128).mem.readAt (chain.add 56#64) 64 = s.h :=
    (MemoryState.readAt_alloca hwf (hc.fits_add (k := 56) (count := 8) (by decide))).trans hm.h
  norm_num only [Nat.cast_ofNat] at hg1 hg2 hg3 hg4 hg5 hg6 hg7
  simp [program.bb0, List.foldlM_cons, List.foldlM_nil, Instr.run,
    coreEntryEnv, entryConstants, hp0, modifyGet_apply,
    Operation.load, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
    Operation.GepSignedRange, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect, throwUBIf,
    hg1, hg2, hg3, hg4, hg5, hg6, hg7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7]
  rfl

theorem coreEntry_block (E : Env program.Γ) (state : GlobalState)
    (kp chain data : Pointer) (n : Nat) (s : State) (hwf : state.WF)
    (hp : E.read (%arg0) = .value chain) (hd : E.read (%arg1) = .value data)
    (hn : E.read (%arg2) = .value (BitVec.ofNat 64 n))
    (hc : SmallRange state.mem chain 64) (hm : ChainMemory state.mem chain s) :
    (program.bb0 kp).run program.blockParams E state =
      .value ((outerNextEnv (coreEntryEnv E kp chain state.allocaPtr s) s data n, .inr 1),
        state.alloca 128) := by
  have hd0 : E.args 1 = .value data := hd
  have hn0 : E.args 2 = .value (BitVec.ofNat 64 n) := hn
  simp only [BasicBlock.run, EffectM.bind_eq,
    coreEntry_body E state kp chain s hwf hp hc hm, PoisonOr.value_bind]
  simp [program.bb0, Exit.run, Jump.run, coreEntryEnv, entryConstants, outerNextEnv,
    hd0, hn0, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    EffectM.pure_eq, mlir_env, mlir_effect]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Core

import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Startup
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-! Actual final Montgomery-body stores and all nine zeroizations/fences.
The output words are parameters supplied by the separate carry arithmetic. -/

set_option maxRecDepth 100000

namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

def outputStores (m : MemoryState) (out : Pointer) (words : Fin 5 → BitVec 64) : MemoryState :=
  let m0 := m.storeAt out (words 0)
  let m1 := m0.storeAt (out.add 8#64) (words 1)
  let m2 := m1.storeAt (out.add 16#64) (words 2)
  let m3 := m2.storeAt (out.add 24#64) (words 3)
  let m4 := m3.storeAt (out.add 32#64) (words 4)
  m4

def zeroizeStores (m : MemoryState) (scratch : Fin 9 → Pointer) : MemoryState :=
  let m1 := m.storeAt (scratch 0) (0#128)
  let m2 := m1.storeAt (scratch 1) (0#128)
  let m3 := m2.storeAt (scratch 2) (0#128)
  let m4 := m3.storeAt (scratch 3) (0#128)
  let m5 := m4.storeAt (scratch 4) (0#128)
  let m6 := m5.storeAt (scratch 5) (0#128)
  let m7 := m6.storeAt (scratch 6) (0#128)
  let m8 := m7.storeAt (scratch 7) (0#128)
  let m9 := m8.storeAt (scratch 8) (0#128)
  m9

def storesEnv (E : Env program.Γ) (out : Pointer) : Env program.Γ :=
  E[%230 := .value (out.add 8#64), %231 := .value (out.add 16#64),
    %232 := .value (out.add 24#64), %233 := .value (out.add 32#64)]

/-- Execute the entire actual store/zeroize suffix. Only output and scratch
liveness is assumed here; the full call proof derives scratch freshness. -/
theorem output_and_zeroize_run (p : Primitives) (E : Env program.Γ)
    (state : GlobalState) (out : Pointer) (words : Fin 5 → BitVec 64)
    (scratch : Fin 9 → Pointer)
    (hout : E.read (%arg0) = .value out)
    (hw0 : E.read (%211) = .value (words 0))
    (hw1 : E.read (%216) = .value (words 1))
    (hw2 : E.read (%221) = .value (words 2))
    (hw3 : E.read (%224) = .value (words 3))
    (hw4 : E.read (%229) = .value (words 4))
    (hs0 : E.read (%24) = .value (scratch 0))
    (hs1 : E.read (%25) = .value (scratch 1))
    (hs2 : E.read (%26) = .value (scratch 2))
    (hs3 : E.read (%27) = .value (scratch 3))
    (hs4 : E.read (%28) = .value (scratch 4))
    (hs5 : E.read (%29) = .value (scratch 5))
    (hs6 : E.read (%30) = .value (scratch 6))
    (hs7 : E.read (%31) = .value (scratch 7))
    (hs8 : E.read (%32) = .value (scratch 8))
    (hk1 : E.read (%1) = .value 8#64)
    (hk2 : E.read (%2) = .value 16#64)
    (hk3 : E.read (%3) = .value 24#64)
    (hk4 : E.read (%4) = .value 32#64)
    (hzero : E.read (%23) = .value 0#128)
    (houtput : SmallRange state.mem out 40)
    (hscratch : ∀ i, Fits state.mem (scratch i) 128) :
    List.foldlM Instr.run E ((program.entry p).body.drop 250) state =
      .value (storesEnv E out,
        {state with mem := zeroizeStores (outputStores state.mem out words) scratch}) := by
  change E.args 0 = .value out at hout
  have hf0 := houtput.fits_add (k := 0) (count := 8) (by decide)
  have hf1 := houtput.fits_add (k := 8) (count := 8) (by decide)
  have hf2 := houtput.fits_add (k := 16) (count := 8) (by decide)
  have hf3 := houtput.fits_add (k := 24) (count := 8) (by decide)
  have hf4 := houtput.fits_add (k := 32) (count := 8) (by decide)
  simp only [Pointer.add_zero] at hf0
  have hfs0 := hscratch 0
  have hfs1 := hscratch 1
  have hfs2 := hscratch 2
  have hfs3 := hscratch 3
  have hfs4 := hscratch 4
  have hfs5 := hscratch 5
  have hfs6 := hscratch 6
  have hfs7 := hscratch 7
  have hfs8 := hscratch 8
  have live1 := houtput.storeAt out (words 0)
  have hg1 := live1.gep (k := 8) (by decide)
  have live2 := live1.storeAt (out.add 8#64) (words 1)
  have hg2 := live2.gep (k := 16) (by decide)
  have live3 := live2.storeAt (out.add 16#64) (words 2)
  have hg3 := live3.gep (k := 24) (by decide)
  have live4 := live3.storeAt (out.add 24#64) (words 3)
  have hg4 := live4.gep (k := 32) (by decide)
  norm_num at hg1 hg2 hg3 hg4
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    Operation.store, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
    Operation.GepSignedRange, outputStores, zeroizeStores, storesEnv,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env, throwUBIf,
    hout, hw0, hw1, hw2, hw3, hw4,
    hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8,
    hk1, hk2, hk3, hk4, hzero,
    hf0, hf1, hf2, hf3, hf4,
    hfs0, hfs1, hfs2, hfs3, hfs4, hfs5, hfs6, hfs7, hfs8,
    hg1, hg2, hg3, hg4]

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

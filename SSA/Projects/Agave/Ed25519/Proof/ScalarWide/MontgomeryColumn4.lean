import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryProduct
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-! One actual product column, its newly encountered loads, and its scratch
store. The multiplication flags are proved for arbitrary u64 limb words. -/

set_option maxRecDepth 100000

namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

def column4Env (E : Env program.Γ) (a b : Fin 5 → BitVec 64)
    (left right : Pointer) : Env program.Γ :=
  let v71 : Pointer := right.add 32#64
  let v72 : BitVec 64 := b 4
  let v73 : BitVec 128 := v72.setWidth 128
  let v74 : BitVec 128 := v73 * ((a 0).setWidth 128)
  let v75 : BitVec 128 := ((b 3).setWidth 128) * ((a 1).setWidth 128)
  let v76 : BitVec 128 := ((a 2).setWidth 128) * ((b 2).setWidth 128)
  let v77 : BitVec 128 := ((a 3).setWidth 128) * ((b 1).setWidth 128)
  let v78 : Pointer := left.add 32#64
  let v79 : BitVec 64 := a 4
  let v80 : BitVec 128 := v79.setWidth 128
  let v81 : BitVec 128 := v80 * ((b 0).setWidth 128)
  let v82 : BitVec 128 := v75 + v76
  let v83 : BitVec 128 := v82 + v77
  let v84 : BitVec 128 := v83 + v74
  let v85 : BitVec 128 := v84 + v81
  E[%71 := .value v71,
    %72 := .value v72,
    %73 := .value v73,
    %74 := .value v74,
    %75 := .value v75,
    %76 := .value v76,
    %77 := .value v77,
    %78 := .value v78,
    %79 := .value v79,
    %80 := .value v80,
    %81 := .value v81,
    %82 := .value v82,
    %83 := .value v83,
    %84 := .value v84,
    %85 := .value v85]

def column4Word (a b : Fin 5 → BitVec 64) (left right : Pointer) : BitVec 128 :=
  let v71 : Pointer := right.add 32#64
  let v72 : BitVec 64 := b 4
  let v73 : BitVec 128 := v72.setWidth 128
  let v74 : BitVec 128 := v73 * ((a 0).setWidth 128)
  let v75 : BitVec 128 := ((b 3).setWidth 128) * ((a 1).setWidth 128)
  let v76 : BitVec 128 := ((a 2).setWidth 128) * ((b 2).setWidth 128)
  let v77 : BitVec 128 := ((a 3).setWidth 128) * ((b 1).setWidth 128)
  let v78 : Pointer := left.add 32#64
  let v79 : BitVec 64 := a 4
  let v80 : BitVec 128 := v79.setWidth 128
  let v81 : BitVec 128 := v80 * ((b 0).setWidth 128)
  let v82 : BitVec 128 := v75 + v76
  let v83 : BitVec 128 := v82 + v77
  let v84 : BitVec 128 := v83 + v74
  let v85 : BitVec 128 := v84 + v81
  v85

theorem column4_run (p : Primitives) (E : Env program.Γ) (state : GlobalState)
    (a b : Fin 5 → BitVec 64) (left right scratch : Pointer)
    (hw35 : E.read (%35) = .value ((a 0).setWidth 128))
    (hw36 : E.read (%36) = .value ((b 0).setWidth 128))
    (hw40 : E.read (%40) = .value ((b 1).setWidth 128))
    (hw44 : E.read (%44) = .value ((a 1).setWidth 128))
    (hw49 : E.read (%49) = .value ((b 2).setWidth 128))
    (hw55 : E.read (%55) = .value ((a 2).setWidth 128))
    (hw60 : E.read (%60) = .value ((b 3).setWidth 128))
    (hw66 : E.read (%66) = .value ((a 3).setWidth 128))
    (hleft : E.read (%arg1) = .value left)
    (hright : E.read (%arg2) = .value right)
    (hoffset : E.read (%4) = .value 32#64)
    (hlive : SmallRange state.mem left 40)
    (hrive : SmallRange state.mem right 40)
    (hread_right : state.mem.readAt (right.add 32#64) 64 = b 4)
    (hread_left : state.mem.readAt (left.add 32#64) 64 = a 4)
    (hscratch : E.read (%28) = .value scratch)
    (hfit : Fits state.mem scratch 128)
    : List.foldlM Instr.run E (((program.entry p).body.drop 86).take 16) state =
      .value (column4Env E a b left right,
        {state with mem := state.mem.storeAt scratch (column4Word a b left right)}) := by
  change E.args 1 = .value left at hleft
  change E.args 2 = .value right at hright
  have hgl := hlive.gep (k := 32) (by decide)
  change Operation.gepInboundsLive state.mem (.value left) [.value (32 : Int)] =
    .value (left.add 32#64) at hgl
  have hgr := hrive.gep (k := 32) (by decide)
  change Operation.gepInboundsLive state.mem (.value right) [.value (32 : Int)] =
    .value (right.add 32#64) at hgr
  have hfl := hlive.fits_add (k := 32) (count := 8) (by decide)
  have hfr := hrive.fits_add (k := 32) (count := 8) (by decide)
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    column4Env, column4Word, widened_mul_nuw,
    hw35, hw36, hw40, hw44, hw49, hw55, hw60, hw66, hscratch, hfit, hleft, hright, hoffset, hgl, hgr, hfl, hfr, hread_left, hread_right,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    Operation.load, Operation.store, Operation.zext, Operation.add,
    UnOp.compute, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

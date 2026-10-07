import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryProduct
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-! One actual product column, its newly encountered loads, and its scratch
store. The multiplication flags are proved for arbitrary u64 limb words. -/

set_option maxRecDepth 100000

namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

def column3Env (E : Env program.Γ) (a b : Fin 5 → BitVec 64)
    (left right : Pointer) : Env program.Γ :=
  let v58 : Pointer := right.add 24#64
  let v59 : BitVec 64 := b 3
  let v60 : BitVec 128 := v59.setWidth 128
  let v61 : BitVec 128 := v60 * ((a 0).setWidth 128)
  let v62 : BitVec 128 := ((b 2).setWidth 128) * ((a 1).setWidth 128)
  let v63 : BitVec 128 := ((a 2).setWidth 128) * ((b 1).setWidth 128)
  let v64 : Pointer := left.add 24#64
  let v65 : BitVec 64 := a 3
  let v66 : BitVec 128 := v65.setWidth 128
  let v67 : BitVec 128 := v66 * ((b 0).setWidth 128)
  let v68 : BitVec 128 := v63 + v62
  let v69 : BitVec 128 := v68 + v61
  let v70 : BitVec 128 := v69 + v67
  E[%58 := .value v58,
    %59 := .value v59,
    %60 := .value v60,
    %61 := .value v61,
    %62 := .value v62,
    %63 := .value v63,
    %64 := .value v64,
    %65 := .value v65,
    %66 := .value v66,
    %67 := .value v67,
    %68 := .value v68,
    %69 := .value v69,
    %70 := .value v70]

def column3Word (a b : Fin 5 → BitVec 64) (left right : Pointer) : BitVec 128 :=
  let v58 : Pointer := right.add 24#64
  let v59 : BitVec 64 := b 3
  let v60 : BitVec 128 := v59.setWidth 128
  let v61 : BitVec 128 := v60 * ((a 0).setWidth 128)
  let v62 : BitVec 128 := ((b 2).setWidth 128) * ((a 1).setWidth 128)
  let v63 : BitVec 128 := ((a 2).setWidth 128) * ((b 1).setWidth 128)
  let v64 : Pointer := left.add 24#64
  let v65 : BitVec 64 := a 3
  let v66 : BitVec 128 := v65.setWidth 128
  let v67 : BitVec 128 := v66 * ((b 0).setWidth 128)
  let v68 : BitVec 128 := v63 + v62
  let v69 : BitVec 128 := v68 + v61
  let v70 : BitVec 128 := v69 + v67
  v70

theorem column3_run (p : Primitives) (E : Env program.Γ) (state : GlobalState)
    (a b : Fin 5 → BitVec 64) (left right scratch : Pointer)
    (hw35 : E.read (%35) = .value ((a 0).setWidth 128))
    (hw36 : E.read (%36) = .value ((b 0).setWidth 128))
    (hw40 : E.read (%40) = .value ((b 1).setWidth 128))
    (hw44 : E.read (%44) = .value ((a 1).setWidth 128))
    (hw49 : E.read (%49) = .value ((b 2).setWidth 128))
    (hw55 : E.read (%55) = .value ((a 2).setWidth 128))
    (hleft : E.read (%arg1) = .value left)
    (hright : E.read (%arg2) = .value right)
    (hoffset : E.read (%3) = .value 24#64)
    (hlive : SmallRange state.mem left 40)
    (hrive : SmallRange state.mem right 40)
    (hread_right : state.mem.readAt (right.add 24#64) 64 = b 3)
    (hread_left : state.mem.readAt (left.add 24#64) 64 = a 3)
    (hscratch : E.read (%27) = .value scratch)
    (hfit : Fits state.mem scratch 128)
    : List.foldlM Instr.run E (((program.entry p).body.drop 72).take 14) state =
      .value (column3Env E a b left right,
        {state with mem := state.mem.storeAt scratch (column3Word a b left right)}) := by
  change E.args 1 = .value left at hleft
  change E.args 2 = .value right at hright
  have hgl := hlive.gep (k := 24) (by decide)
  change Operation.gepInboundsLive state.mem (.value left) [.value (24 : Int)] =
    .value (left.add 24#64) at hgl
  have hgr := hrive.gep (k := 24) (by decide)
  change Operation.gepInboundsLive state.mem (.value right) [.value (24 : Int)] =
    .value (right.add 24#64) at hgr
  have hfl := hlive.fits_add (k := 24) (count := 8) (by decide)
  have hfr := hrive.fits_add (k := 24) (count := 8) (by decide)
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    column3Env, column3Word, widened_mul_nuw,
    hw35, hw36, hw40, hw44, hw49, hw55, hscratch, hfit, hleft, hright, hoffset, hgl, hgr, hfl, hfr, hread_left, hread_right,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    Operation.load, Operation.store, Operation.zext, Operation.add,
    UnOp.compute, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

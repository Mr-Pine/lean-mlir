import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryProduct
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-! One actual product column, its newly encountered loads, and its scratch
store. The multiplication flags are proved for arbitrary u64 limb words. -/

set_option maxRecDepth 100000

namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

def column2Env (E : Env program.Γ) (a b : Fin 5 → BitVec 64)
    (left right : Pointer) : Env program.Γ :=
  let v47 : Pointer := right.add 16#64
  let v48 : BitVec 64 := b 2
  let v49 : BitVec 128 := v48.setWidth 128
  let v50 : BitVec 128 := v49 * ((a 0).setWidth 128)
  let v51 : BitVec 128 := ((a 1).setWidth 128) * ((b 1).setWidth 128)
  let v52 : BitVec 128 := v50 + v51
  let v53 : Pointer := left.add 16#64
  let v54 : BitVec 64 := a 2
  let v55 : BitVec 128 := v54.setWidth 128
  let v56 : BitVec 128 := v55 * ((b 0).setWidth 128)
  let v57 : BitVec 128 := v52 + v56
  E[%47 := .value v47,
    %48 := .value v48,
    %49 := .value v49,
    %50 := .value v50,
    %51 := .value v51,
    %52 := .value v52,
    %53 := .value v53,
    %54 := .value v54,
    %55 := .value v55,
    %56 := .value v56,
    %57 := .value v57]

def column2Word (a b : Fin 5 → BitVec 64) (left right : Pointer) : BitVec 128 :=
  let v47 : Pointer := right.add 16#64
  let v48 : BitVec 64 := b 2
  let v49 : BitVec 128 := v48.setWidth 128
  let v50 : BitVec 128 := v49 * ((a 0).setWidth 128)
  let v51 : BitVec 128 := ((a 1).setWidth 128) * ((b 1).setWidth 128)
  let v52 : BitVec 128 := v50 + v51
  let v53 : Pointer := left.add 16#64
  let v54 : BitVec 64 := a 2
  let v55 : BitVec 128 := v54.setWidth 128
  let v56 : BitVec 128 := v55 * ((b 0).setWidth 128)
  let v57 : BitVec 128 := v52 + v56
  v57

theorem column2_run (p : Primitives) (E : Env program.Γ) (state : GlobalState)
    (a b : Fin 5 → BitVec 64) (left right scratch : Pointer)
    (hw35 : E.read (%35) = .value ((a 0).setWidth 128))
    (hw36 : E.read (%36) = .value ((b 0).setWidth 128))
    (hw40 : E.read (%40) = .value ((b 1).setWidth 128))
    (hw44 : E.read (%44) = .value ((a 1).setWidth 128))
    (hleft : E.read (%arg1) = .value left)
    (hright : E.read (%arg2) = .value right)
    (hoffset : E.read (%2) = .value 16#64)
    (hlive : SmallRange state.mem left 40)
    (hrive : SmallRange state.mem right 40)
    (hread_right : state.mem.readAt (right.add 16#64) 64 = b 2)
    (hread_left : state.mem.readAt (left.add 16#64) 64 = a 2)
    (hscratch : E.read (%26) = .value scratch)
    (hfit : Fits state.mem scratch 128)
    : List.foldlM Instr.run E (((program.entry p).body.drop 60).take 12) state =
      .value (column2Env E a b left right,
        {state with mem := state.mem.storeAt scratch (column2Word a b left right)}) := by
  change E.args 1 = .value left at hleft
  change E.args 2 = .value right at hright
  have hgl := hlive.gep (k := 16) (by decide)
  change Operation.gepInboundsLive state.mem (.value left) [.value (16 : Int)] =
    .value (left.add 16#64) at hgl
  have hgr := hrive.gep (k := 16) (by decide)
  change Operation.gepInboundsLive state.mem (.value right) [.value (16 : Int)] =
    .value (right.add 16#64) at hgr
  have hfl := hlive.fits_add (k := 16) (count := 8) (by decide)
  have hfr := hrive.fits_add (k := 16) (count := 8) (by decide)
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    column2Env, column2Word, widened_mul_nuw,
    hw35, hw36, hw40, hw44, hscratch, hfit, hleft, hright, hoffset, hgl, hgr, hfl, hfr, hread_left, hread_right,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    Operation.load, Operation.store, Operation.zext, Operation.add,
    UnOp.compute, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

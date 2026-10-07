import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryProduct
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-! One actual product column, its newly encountered loads, and its scratch
store. The multiplication flags are proved for arbitrary u64 limb words. -/

set_option maxRecDepth 100000

namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

def column1Env (E : Env program.Γ) (a b : Fin 5 → BitVec 64)
    (left right : Pointer) : Env program.Γ :=
  let v38 : Pointer := right.add 8#64
  let v39 : BitVec 64 := b 1
  let v40 : BitVec 128 := v39.setWidth 128
  let v41 : BitVec 128 := v40 * ((a 0).setWidth 128)
  let v42 : Pointer := left.add 8#64
  let v43 : BitVec 64 := a 1
  let v44 : BitVec 128 := v43.setWidth 128
  let v45 : BitVec 128 := v44 * ((b 0).setWidth 128)
  let v46 : BitVec 128 := v45 + v41
  E[%38 := .value v38,
    %39 := .value v39,
    %40 := .value v40,
    %41 := .value v41,
    %42 := .value v42,
    %43 := .value v43,
    %44 := .value v44,
    %45 := .value v45,
    %46 := .value v46]

def column1Word (a b : Fin 5 → BitVec 64) (left right : Pointer) : BitVec 128 :=
  let v38 : Pointer := right.add 8#64
  let v39 : BitVec 64 := b 1
  let v40 : BitVec 128 := v39.setWidth 128
  let v41 : BitVec 128 := v40 * ((a 0).setWidth 128)
  let v42 : Pointer := left.add 8#64
  let v43 : BitVec 64 := a 1
  let v44 : BitVec 128 := v43.setWidth 128
  let v45 : BitVec 128 := v44 * ((b 0).setWidth 128)
  let v46 : BitVec 128 := v45 + v41
  v46

theorem column1_run (p : Primitives) (E : Env program.Γ) (state : GlobalState)
    (a b : Fin 5 → BitVec 64) (left right scratch : Pointer)
    (hw35 : E.read (%35) = .value ((a 0).setWidth 128))
    (hw36 : E.read (%36) = .value ((b 0).setWidth 128))
    (hleft : E.read (%arg1) = .value left)
    (hright : E.read (%arg2) = .value right)
    (hoffset : E.read (%1) = .value 8#64)
    (hlive : SmallRange state.mem left 40)
    (hrive : SmallRange state.mem right 40)
    (hread_right : state.mem.readAt (right.add 8#64) 64 = b 1)
    (hread_left : state.mem.readAt (left.add 8#64) 64 = a 1)
    (hscratch : E.read (%25) = .value scratch)
    (hfit : Fits state.mem scratch 128)
    : List.foldlM Instr.run E (((program.entry p).body.drop 50).take 10) state =
      .value (column1Env E a b left right,
        {state with mem := state.mem.storeAt scratch (column1Word a b left right)}) := by
  change E.args 1 = .value left at hleft
  change E.args 2 = .value right at hright
  have hgl := hlive.gep (k := 8) (by decide)
  change Operation.gepInboundsLive state.mem (.value left) [.value (8 : Int)] =
    .value (left.add 8#64) at hgl
  have hgr := hrive.gep (k := 8) (by decide)
  change Operation.gepInboundsLive state.mem (.value right) [.value (8 : Int)] =
    .value (right.add 8#64) at hgr
  have hfl := hlive.fits_add (k := 8) (count := 8) (by decide)
  have hfr := hrive.fits_add (k := 8) (count := 8) (by decide)
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    column1Env, column1Word, widened_mul_nuw,
    hw35, hw36, hscratch, hfit, hleft, hright, hoffset, hgl, hgr, hfl, hfr, hread_left, hread_right,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    Operation.load, Operation.store, Operation.zext, Operation.add,
    UnOp.compute, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

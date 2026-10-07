import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryProduct
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-! One actual product column, its newly encountered loads, and its scratch
store. The multiplication flags are proved for arbitrary u64 limb words. -/

set_option maxRecDepth 100000

namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

def column5Env (E : Env program.Γ) (a b : Fin 5 → BitVec 64)
    (left right : Pointer) : Env program.Γ :=
  let v86 : BitVec 128 := ((b 4).setWidth 128) * ((a 1).setWidth 128)
  let v87 : BitVec 128 := ((b 3).setWidth 128) * ((a 2).setWidth 128)
  let v88 : BitVec 128 := ((a 3).setWidth 128) * ((b 2).setWidth 128)
  let v89 : BitVec 128 := ((a 4).setWidth 128) * ((b 1).setWidth 128)
  let v90 : BitVec 128 := v88 + v87
  let v91 : BitVec 128 := v90 + v86
  let v92 : BitVec 128 := v91 + v89
  E[%86 := .value v86,
    %87 := .value v87,
    %88 := .value v88,
    %89 := .value v89,
    %90 := .value v90,
    %91 := .value v91,
    %92 := .value v92]

def column5Word (a b : Fin 5 → BitVec 64) (left right : Pointer) : BitVec 128 :=
  let v86 : BitVec 128 := ((b 4).setWidth 128) * ((a 1).setWidth 128)
  let v87 : BitVec 128 := ((b 3).setWidth 128) * ((a 2).setWidth 128)
  let v88 : BitVec 128 := ((a 3).setWidth 128) * ((b 2).setWidth 128)
  let v89 : BitVec 128 := ((a 4).setWidth 128) * ((b 1).setWidth 128)
  let v90 : BitVec 128 := v88 + v87
  let v91 : BitVec 128 := v90 + v86
  let v92 : BitVec 128 := v91 + v89
  v92

theorem column5_run (p : Primitives) (E : Env program.Γ) (state : GlobalState)
    (a b : Fin 5 → BitVec 64) (left right scratch : Pointer)
    (hw40 : E.read (%40) = .value ((b 1).setWidth 128))
    (hw44 : E.read (%44) = .value ((a 1).setWidth 128))
    (hw49 : E.read (%49) = .value ((b 2).setWidth 128))
    (hw55 : E.read (%55) = .value ((a 2).setWidth 128))
    (hw60 : E.read (%60) = .value ((b 3).setWidth 128))
    (hw66 : E.read (%66) = .value ((a 3).setWidth 128))
    (hw73 : E.read (%73) = .value ((b 4).setWidth 128))
    (hw80 : E.read (%80) = .value ((a 4).setWidth 128))
    (hscratch : E.read (%29) = .value scratch)
    (hfit : Fits state.mem scratch 128)
    : List.foldlM Instr.run E (((program.entry p).body.drop 102).take 8) state =
      .value (column5Env E a b left right,
        {state with mem := state.mem.storeAt scratch (column5Word a b left right)}) := by
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    column5Env, column5Word, widened_mul_nuw,
    hw40, hw44, hw49, hw55, hw60, hw66, hw73, hw80, hscratch, hfit,
    Operation.load, Operation.store, Operation.zext, Operation.add,
    UnOp.compute, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

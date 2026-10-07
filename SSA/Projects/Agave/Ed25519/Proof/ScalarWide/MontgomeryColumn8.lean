import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryProduct
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-! One actual product column, its newly encountered loads, and its scratch
store. The multiplication flags are proved for arbitrary u64 limb words. -/

set_option maxRecDepth 100000

namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

def column8Env (E : Env program.Γ) (a b : Fin 5 → BitVec 64)
    (left right : Pointer) : Env program.Γ :=
  let v101 : BitVec 128 := ((a 4).setWidth 128) * ((b 4).setWidth 128)
  E[%101 := .value v101]

def column8Word (a b : Fin 5 → BitVec 64) (left right : Pointer) : BitVec 128 :=
  let v101 : BitVec 128 := ((a 4).setWidth 128) * ((b 4).setWidth 128)
  v101

theorem column8_run (p : Primitives) (E : Env program.Γ) (state : GlobalState)
    (a b : Fin 5 → BitVec 64) (left right scratch : Pointer)
    (hw73 : E.read (%73) = .value ((b 4).setWidth 128))
    (hw80 : E.read (%80) = .value ((a 4).setWidth 128))
    (hscratch : E.read (%32) = .value scratch)
    (hfit : Fits state.mem scratch 128)
    : List.foldlM Instr.run E (((program.entry p).body.drop 120).take 2) state =
      .value (column8Env E a b left right,
        {state with mem := state.mem.storeAt scratch (column8Word a b left right)}) := by
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    column8Env, column8Word, widened_mul_nuw,
    hw73, hw80, hscratch, hfit,
    Operation.load, Operation.store, Operation.zext, Operation.add,
    UnOp.compute, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

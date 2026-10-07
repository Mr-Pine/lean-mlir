import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.WrapperBorrow
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.WrapperAddback
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryTail
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Linked

/-! Complete wrapper conditional-subtraction phase, including the actual byte
black-box call and its allocation. Stops before the five result-slot stores. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
open Subtraction
set_option maxRecDepth 100000

structure WrapperSubtractReady (E : Env program.Γ) (x : Fin 5 → BitVec 52) : Prop where
  x0 : E.read (%288) = .value ((x 0).setWidth 64)
  x1 : E.read (%294) = .value ((x 1).setWidth 64)
  x2 : E.read (%300) = .value ((x 2).setWidth 64)
  x3 : E.read (%306) = .value ((x 3).setWidth 64)
  x4 : E.read (%312) = .value ((x 4).setWidth 64)
  c32 : E.read (%32) = .value (52 : BitVec 64)
  c38 : E.read (%38) = .value (4503599627370495 : BitVec 64)
  c41 : E.read (%41) = .value (-671914833335277 : BitVec 64)
  c42 : E.read (%42) = .value (63 : BitVec 64)
  c43 : E.read (%43) = .value (-3916664325105025 : BitVec 64)
  c44 : E.read (%44) = .value (-1367801 : BitVec 64)
  c45 : E.read (%45) = .value (-17592186044416 : BitVec 64)
  c46 : E.read (%46) = .value (0 : BitVec 64)
  c47 : E.read (%47) = .value (671914833335277 : BitVec 64)
  c48 : E.read (%48) = .value (3916664325105025 : BitVec 64)
  c49 : E.read (%49) = .value (1367801 : BitVec 64)
  c50 : E.read (%50) = .value (17592186044416 : BitVec 64)

def wrapperSubtractEnv (E : Env program.Γ) (x : Fin 5 → BitVec 52) : Env program.Γ :=
  let d := differences (x 0) (x 1) (x 2) (x 3) (x 4)
  wrapperAddbackEnv ((wrapperBorrowEnv E x)[%331 := .value (borrowByte d)])
    (ScalarMontgomeryMul.tailLow x) (d 4) (borrowByte d)

theorem wrapper_subtract_run (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (x : Fin 5 → BitVec 52)
    (hr : WrapperSubtractReady E x) (hwf : state.WF) :
    (program.entry linkedPrimitives g).runBodyFrom E 358 state =
      (program.entry linkedPrimitives g).runBodyFrom (wrapperSubtractEnv E x) 400
        {state with alloc := (state.alloca 1).alloc} := by
  let d := differences (x 0) (x 1) (x 2) (x 3) (x 4)
  let byte := borrowByte d
  let E1 := wrapperBorrowEnv E x
  let E2 := E1[%331 := .value byte]
  let state1 : GlobalState := {state with alloc := (state.alloca 1).alloc}
  have hborrow := wrapper_borrow_run linkedPrimitives g E state x
    hr.x0 hr.x1 hr.x2 hr.x3 hr.x4 hr.c38 hr.c41 hr.c42 hr.c43 hr.c44 hr.c45
  have hcall : linkedPrimitives.blackBoxByte (.cons (.value byte) .nil) state =
      .value (.cons (.value byte) .nil, state1) :=
    Agave.Ed25519.Encoding.Decompress.Execution.BlackBox.program_call byte state hwf
  have hbyte : E1.read (%330) = .value byte := by
    simp [E1, byte, d, wrapperBorrowEnv, mlir_env]
  have hlow (i : Fin 4) : (ScalarMontgomeryMul.tailLow x i).toNat < 2 ^ 52 := by
    rw [ScalarMontgomeryMul.tailLow, ScalarMontgomeryMul.mask52_toNat]
    exact Nat.mod_lt _ (by decide)
  have hc32 := hr.c32
  have hc38 := hr.c38
  have hc41 := hr.c41
  have hc42 := hr.c42
  have hc43 := hr.c43
  have hc44 := hr.c44
  have hc45 := hr.c45
  have hc46 := hr.c46
  have hc47 := hr.c47
  have hc48 := hr.c48
  have hc49 := hr.c49
  have hc50 := hr.c50
  have hadd : List.foldlM Instr.run E2
      (((program.entry linkedPrimitives g).body.drop 377).take 23) state1 =
      .value (wrapperSubtractEnv E x, state1) := by
    apply wrapper_addback_run linkedPrimitives g E2 state1
      (ScalarMontgomeryMul.tailLow x) (d 4) byte hlow
      ((differences_top_certificate x).2.2) <;>
      simp [E2, E1, wrapperBorrowEnv, ScalarMontgomeryMul.tailLow, d, byte,
        hc32, hc38, hc41, hc42, hc43, hc44, hc45, hc46, hc47, hc48, hc49, hc50, mlir_env]
  exact (ScalarMontgomeryMul.runBodyFrom_chunk hborrow).trans
    ((conditional_subtraction_black_box_call linkedPrimitives g E1 state state1 byte hbyte hcall).trans
      (ScalarMontgomeryMul.runBodyFrom_chunk hadd))

theorem wrapperSubtractEnv_words (E : Env program.Γ) (x : Fin 5 → BitVec 52) :
    (wrapperSubtractEnv E x).read (%336) = .value (ScalarMontgomeryMul.tailWords x 0) ∧
    (wrapperSubtractEnv E x).read (%341) = .value (ScalarMontgomeryMul.tailWords x 1) ∧
    (wrapperSubtractEnv E x).read (%346) = .value (ScalarMontgomeryMul.tailWords x 2) ∧
    (wrapperSubtractEnv E x).read (%349) = .value (ScalarMontgomeryMul.tailWords x 3) ∧
    (wrapperSubtractEnv E x).read (%354) = .value (ScalarMontgomeryMul.tailWords x 4) := by
  exact wrapperAddbackEnv_words _ _

end Agave.Ed25519.Verifier.Execution.ScalarWide

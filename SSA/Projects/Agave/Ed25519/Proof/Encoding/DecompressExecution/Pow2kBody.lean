import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Pow2kWords
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Pow2kProgram

namespace Agave.Ed25519.Encoding.Decompress.Execution.Pow2k
open LeanMLIR.RIR
open SerialFieldMul
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

abbrev loopEnv (E : ⟪program.Γ⟫) (a : Words) (count : BitVec 32) : ⟪program.Γ⟫ :=
  E[%4 := .value 19#64, %5 := .value 1#128,
    %6 := .value 51#128, %7 := .value 18446744073709551615#128,
    %8 := .value 2251799813685247#64, %9 := .value 51#64,
    %10 := .value 4294967295#32, %11 := .value 0#32,
    %21 := .value (a 4), %22 := .value (a 3), %23 := .value (a 2),
    %24 := .value (a 1), %25 := .value (a 0), %26 := .value count]

theorem loopEnv_args (E : ⟪program.Γ⟫) (a : Words) (count : BitVec 32) :
    (loopEnv E a count).args = E.args := by
  simp only [loopEnv, Env.write_args]

/-- Total register evaluation of the loop's pure scalar instructions. Poisoned
registers stay poisoned; the actual loop body has no memory instructions. -/
def scalarStep (E : ⟪program.Γ⟫) : Instr program.Γ → ⟪program.Γ⟫
  | .unop op dst a => E.write dst (op.compute (E.read a))
  | .binop op dst a b => E.write dst (op.compute (E.read a) (E.read b))
  | _ => E

def bodyEnv (E : ⟪program.Γ⟫) : ⟪program.Γ⟫ :=
  program.bb1.body.foldl scalarStep E

theorem body_run (E : ⟪program.Γ⟫) (s : GlobalState) :
    program.bb1.runBodyFrom E 0 s = .value (bodyEnv E, s) := by
  dsimp only [bodyEnv, program.bb1, BasicBlock.runBodyFrom, List.drop]
  simp only [List.foldlM_cons, List.foldlM_nil, List.foldl_cons, List.foldl_nil,
    scalarStep, Instr.run, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]

attribute [local irreducible] BinOp.compute UnOp.compute

open Lean Meta in
/-- Evaluate only the selected register before simplifying its value. -/
dsimproc_decl reduceComputedRead (Env.read _ _) := fun e => do
  let e' ← withTransparency .default (whnf e)
  return if e' == e then .continue else .visit e'

attribute [-simp] BitVec.shiftLeft_add_distrib in
set_option maxRecDepth 20000 in
theorem bodyEnv_read94 (E : ⟪program.Γ⟫) (a : Words) (count : BitVec 32) :
    (bodyEnv (loopEnv E a count)).read (%94) = .value (SerialPoint.squareMachine a 0) := by
  simp [↓reduceComputedRead, mlir_instr, mlir_operation,
    wide_mul_nooverflow, final_add_nooverflow, SerialPoint.squareMachine,
    SerialPoint.squareWordColumns, wordSchedule]

attribute [-simp] BitVec.shiftLeft_add_distrib in
theorem bodyEnv_read93 (E : ⟪program.Γ⟫) (a : Words) (count : BitVec 32) :
    (bodyEnv (loopEnv E a count)).read (%93) = .value (SerialPoint.squareMachine a 1) := by
  simp [↓reduceComputedRead, mlir_instr, mlir_operation,
    wide_mul_nooverflow, final_add_nooverflow, SerialPoint.squareMachine,
    SerialPoint.squareWordColumns, wordSchedule]

attribute [-simp] BitVec.shiftLeft_add_distrib in
theorem bodyEnv_read80 (E : ⟪program.Γ⟫) (a : Words) (count : BitVec 32) :
    (bodyEnv (loopEnv E a count)).read (%80) = .value (SerialPoint.squareMachine a 2) := by
  simp [↓reduceComputedRead, mlir_instr, mlir_operation,
    wide_mul_nooverflow, final_add_nooverflow, SerialPoint.squareMachine,
    SerialPoint.squareWordColumns, wordSchedule]

attribute [-simp] BitVec.shiftLeft_add_distrib in
theorem bodyEnv_read85 (E : ⟪program.Γ⟫) (a : Words) (count : BitVec 32) :
    (bodyEnv (loopEnv E a count)).read (%85) = .value (SerialPoint.squareMachine a 3) := by
  simp [↓reduceComputedRead, mlir_instr, mlir_operation,
    wide_mul_nooverflow, final_add_nooverflow, SerialPoint.squareMachine,
    SerialPoint.squareWordColumns, wordSchedule]

attribute [-simp] BitVec.shiftLeft_add_distrib in
theorem bodyEnv_read89 (E : ⟪program.Γ⟫) (a : Words) (count : BitVec 32) :
    (bodyEnv (loopEnv E a count)).read (%89) = .value (SerialPoint.squareMachine a 4) := by
  simp [↓reduceComputedRead, mlir_instr, mlir_operation,
    wide_mul_nooverflow, final_add_nooverflow, SerialPoint.squareMachine,
    SerialPoint.squareWordColumns, wordSchedule]

private theorem scalarStep_args (E : ⟪program.Γ⟫) (i : Instr program.Γ) :
    (scalarStep E i).args = E.args := by cases i <;> rfl

theorem bodyEnv_args (E : ⟪program.Γ⟫) : (bodyEnv E).args = E.args := by
  have preserve (l : List (Instr program.Γ)) (E : ⟪program.Γ⟫) :
      (l.foldl scalarStep E).args = E.args := by
    induction l generalizing E with
    | nil => rfl
    | cons i l ih => exact (ih (scalarStep E i)).trans (scalarStep_args E i)
  exact preserve _ E

theorem bodyEnv_read4 (E : ⟪program.Γ⟫) (a : Words) (count : BitVec 32) :
    (bodyEnv (loopEnv E a count)).read (%4) = .value 19#64 := rfl

theorem bodyEnv_read5 (E : ⟪program.Γ⟫) (a : Words) (count : BitVec 32) :
    (bodyEnv (loopEnv E a count)).read (%5) = .value 1#128 := rfl

theorem bodyEnv_read6 (E : ⟪program.Γ⟫) (a : Words) (count : BitVec 32) :
    (bodyEnv (loopEnv E a count)).read (%6) = .value 51#128 := rfl

theorem bodyEnv_read7 (E : ⟪program.Γ⟫) (a : Words) (count : BitVec 32) :
    (bodyEnv (loopEnv E a count)).read (%7) = .value 18446744073709551615#128 := rfl

theorem bodyEnv_read8 (E : ⟪program.Γ⟫) (a : Words) (count : BitVec 32) :
    (bodyEnv (loopEnv E a count)).read (%8) = .value 2251799813685247#64 := rfl

theorem bodyEnv_read9 (E : ⟪program.Γ⟫) (a : Words) (count : BitVec 32) :
    (bodyEnv (loopEnv E a count)).read (%9) = .value 51#64 := rfl

theorem bodyEnv_read10 (E : ⟪program.Γ⟫) (a : Words) (count : BitVec 32) :
    (bodyEnv (loopEnv E a count)).read (%10) = .value 4294967295#32 := rfl

theorem bodyEnv_read11 (E : ⟪program.Γ⟫) (a : Words) (count : BitVec 32) :
    (bodyEnv (loopEnv E a count)).read (%11) = .value 0#32 := rfl

theorem bodyEnv_read95 (E : ⟪program.Γ⟫) (a : Words) (count : BitVec 32) :
    (bodyEnv (loopEnv E a count)).read (%95) = .value (count + 4294967295#32) := by
  simp [↓reduceComputedRead, mlir_instr, mlir_operation]

theorem bodyEnv_read96 (E : ⟪program.Γ⟫) (a : Words) (count : BitVec 32) :
    (bodyEnv (loopEnv E a count)).read (%96) =
      .value (BitVec.ofBool (count + 4294967295#32 == 0#32)) := by
  have h : (bodyEnv (loopEnv E a count)).read (%96) =
      (BinOp.icmp IntPred.eq).compute
        ((bodyEnv (loopEnv E a count)).read (%95))
        ((bodyEnv (loopEnv E a count)).read (%11)) := by rfl
  rw [h, bodyEnv_read95, bodyEnv_read11]
  simp [BinOp.compute, Operation.icmp]

/-- Reinstalling the loop constants leaves the evaluated environment unchanged. -/
theorem bodyEnv_constants (E : ⟪program.Γ⟫) (a : Words) (count : BitVec 32) :
    (bodyEnv (loopEnv E a count))[%4 := .value 19#64, %5 := .value 1#128,
      %6 := .value 51#128, %7 := .value 18446744073709551615#128,
      %8 := .value 2251799813685247#64, %9 := .value 51#64,
      %10 := .value 4294967295#32, %11 := .value 0#32] =
      bodyEnv (loopEnv E a count) := by
  refine Env.write_eq_of ?_ (bodyEnv_read11 E a count)
  refine Env.write_eq_of ?_ (bodyEnv_read10 E a count)
  refine Env.write_eq_of ?_ (bodyEnv_read9 E a count)
  refine Env.write_eq_of ?_ (bodyEnv_read8 E a count)
  refine Env.write_eq_of ?_ (bodyEnv_read7 E a count)
  refine Env.write_eq_of ?_ (bodyEnv_read6 E a count)
  refine Env.write_eq_of ?_ (bodyEnv_read5 E a count)
  exact Env.write_eq_of rfl (bodyEnv_read4 E a count)


end Agave.Ed25519.Encoding.Decompress.Execution.Pow2k

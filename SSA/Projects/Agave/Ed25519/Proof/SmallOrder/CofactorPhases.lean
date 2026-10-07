import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.PointMulByPow2Program
import SSA.Projects.RIR.Run.Tactic

/-! Source slices and fixed-k loop control for mul_by_pow_2. The caller uses
k=3, so the loop has two iterations and the separate return block performs the
third double. No arbitrary-k termination theorem is needed by the verifier. -/
namespace Agave.Ed25519.SmallOrder.Execution.CofactorPhases
open LeanMLIR.RIR Verifier.Execution.PointMulByPow2
set_option maxRecDepth 10000

abbrev loopPrefix (p : Primitives) := (program.bb3 p).body.take 8
abbrev loopTest (p : Primitives) := (program.bb3 p).body.drop 8

theorem loop_body_decomposition (p : Primitives) : (program.bb3 p).body =
    loopPrefix p ++ loopTest p := rfl

theorem loop_test_exact (p : Primitives) : loopTest p =
    [.binop (.icmp .eq) (%29) (%28) (%14)] := rfl

theorem block_three (p : Primitives) : (program p).blocks 3 = program.bb3 p := rfl

theorem loop_exit_exact (p : Primitives) : (program.bb3 p).exit =
    .condBr (%29) ⟨2, .nil⟩ ⟨3, .cons (%28) .nil⟩ := rfl

theorem params_two : program.blockParams 2 = .nil := rfl
theorem params_three : program.blockParams 3 = .cons (%27) .nil := rfl

/-- The first loop body's actual comparison and branch continue with counter
one; all calls, the copy, and the flagged increment are in `loopPrefix`. -/
theorem first_loop_edge (p : Primitives) (E F : Env program.Γ)
    (s t : GlobalState)
    (hp : List.foldlM Instr.run E (loopPrefix p) s = .value (F, t))
    (hnext : F.read (%28) = .value 1#32)
    (hlimit : F.read (%14) = .value 2#32) :
    (program p).runFrom E 3 s =
      (program p).runFrom (F[%29 := .value 0#1, %27 := .value 1#32]) 3 t := by
  have hb : (program.bb3 p).run program.blockParams E s =
      .value ((F[%29 := .value 0#1, %27 := .value 1#32], .inr 3), t) := by
    simp [BasicBlock.run, loop_body_decomposition, List.foldlM_append,
      loop_test_exact, EffectM.bind_eq, hp, PoisonOr.value_bind,
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
      Operation.icmp, EffectM.pure_eq, hnext, hlimit,
      loop_exit_exact, Exit.run, Jump.run, Regs.read_cons, Regs.read_nil,
      Env.writeMany_cons, Env.writeMany_nil, params_two, params_three, mlir_env]
  rw [Func.runFrom_eq, block_three, hb]
  rfl

/-- Counter two selects the separate final-double block, with no third loop
iteration and no loop-bound or no-overflow hypothesis hidden in the branch. -/
theorem second_loop_edge (p : Primitives) (E F : Env program.Γ)
    (s t : GlobalState)
    (hp : List.foldlM Instr.run E (loopPrefix p) s = .value (F, t))
    (hnext : F.read (%28) = .value 2#32)
    (hlimit : F.read (%14) = .value 2#32) :
    (program p).runFrom E 3 s =
      (program p).runFrom (F[%29 := .value 1#1]) 2 t := by
  have hb : (program.bb3 p).run program.blockParams E s =
      .value ((F[%29 := .value 1#1], .inr 2), t) := by
    simp [BasicBlock.run, loop_body_decomposition, List.foldlM_append,
      loop_test_exact, EffectM.bind_eq, hp, PoisonOr.value_bind,
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
      Operation.icmp, EffectM.pure_eq, hnext, hlimit,
      loop_exit_exact, Exit.run, Jump.run, Regs.read_cons, Regs.read_nil,
      Env.writeMany_cons, Env.writeMany_nil, params_two, params_three, mlir_env]
  rw [Func.runFrom_eq, block_three, hb]
  rfl

end Agave.Ed25519.SmallOrder.Execution.CofactorPhases

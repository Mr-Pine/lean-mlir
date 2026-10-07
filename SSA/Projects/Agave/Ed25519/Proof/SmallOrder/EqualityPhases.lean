import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.PointConstantTimeEqProgram
import SSA.Projects.RIR.Run.Tactic

/-! Exact source-order phases of point equality. The two serializer phases
are distinct copies of the same compiler schedule; neither is abstracted away.
All phases use the original function's environment and memory state. -/
namespace Agave.Ed25519.SmallOrder.Execution.EqualityPhases
open LeanMLIR.RIR Verifier.Execution.PointConstantTimeEq
set_option maxRecDepth 16000

abbrev prepare (p : Primitives) := (program.entry p).body.take 55
abbrev productsX (p : Primitives) := ((program.entry p).body.drop 55).take 6
abbrev serializeX (p : Primitives) := ((program.entry p).body.drop 61).take 374
abbrev compareX (p : Primitives) := ((program.entry p).body.drop 435).take 3
abbrev productsY (p : Primitives) := ((program.entry p).body.drop 438).take 6
abbrev serializeY (p : Primitives) := ((program.entry p).body.drop 444).take 374
abbrev compareY (p : Primitives) := ((program.entry p).body.drop 818).take 3
abbrev finish (p : Primitives) := (program.entry p).body.drop 821

theorem body_decomposition (p : Primitives) : (program.entry p).body =
    prepare p ++ productsX p ++ serializeX p ++ compareX p ++ productsY p ++
      serializeY p ++ compareY p ++ finish p := rfl

theorem block_zero (p : Primitives) : (program p).blocks 0 = program.entry p := rfl

theorem entry_exit (p : Primitives) :
    (program.entry p).exit = .ret (.cons (%670) .nil) := rfl

/-- Executions of disjoint instruction phases compose to execution of the
original body, including its actual return instruction. There is no substituted
point-equality oracle or assumed whole-function call result. -/
theorem runFrom_of_phases (p : Primitives)
    (E0 E1 E2 E3 E4 E5 E6 E7 E8 : Env program.Γ)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 : GlobalState) (result : BitVec 8)
    (h0 : List.foldlM Instr.run E0 (prepare p) s0 = .value (E1, s1))
    (h1 : List.foldlM Instr.run E1 (productsX p) s1 = .value (E2, s2))
    (h2 : List.foldlM Instr.run E2 (serializeX p) s2 = .value (E3, s3))
    (h3 : List.foldlM Instr.run E3 (compareX p) s3 = .value (E4, s4))
    (h4 : List.foldlM Instr.run E4 (productsY p) s4 = .value (E5, s5))
    (h5 : List.foldlM Instr.run E5 (serializeY p) s5 = .value (E6, s6))
    (h6 : List.foldlM Instr.run E6 (compareY p) s6 = .value (E7, s7))
    (h7 : List.foldlM Instr.run E7 (finish p) s7 = .value (E8, s8))
    (hr : E8.read (%670) = .value result) :
    (program p).runFrom E0 0 s0 = .value (.cons (.value result) .nil, s8) := by
  have hbody : (program.entry p).run program.blockParams E0 s0 =
      .value ((E8, .inl (.cons (.value result) .nil)), s8) := by
    simp only [BasicBlock.run, body_decomposition, List.foldlM_append,
      EffectM.bind_eq, h0, h1, h2, h3, h4, h5, h6, h7,
      PoisonOr.value_bind, entry_exit, Exit.run, Regs.read_cons, Regs.read_nil,
      hr, EffectM.pure_eq]
  rw [Func.runFrom_eq, block_zero, hbody]
  rfl

/-- Account for the original function's private-frame reclamation rather than
claiming literal state identity after its eight local allocations. -/
theorem call_of_phases (p : Primitives) (args : Vals program.Γ.args)
    (E1 E2 E3 E4 E5 E6 E7 E8 : Env program.Γ)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 : GlobalState) (result : BitVec 8)
    (h0 : List.foldlM Instr.run (Env.init args.get) (prepare p) s0 = .value (E1, s1))
    (h1 : List.foldlM Instr.run E1 (productsX p) s1 = .value (E2, s2))
    (h2 : List.foldlM Instr.run E2 (serializeX p) s2 = .value (E3, s3))
    (h3 : List.foldlM Instr.run E3 (compareX p) s3 = .value (E4, s4))
    (h4 : List.foldlM Instr.run E4 (productsY p) s4 = .value (E5, s5))
    (h5 : List.foldlM Instr.run E5 (serializeY p) s5 = .value (E6, s6))
    (h6 : List.foldlM Instr.run E6 (compareY p) s6 = .value (E7, s7))
    (h7 : List.foldlM Instr.run E7 (finish p) s7 = .value (E8, s8))
    (hr : E8.read (%670) = .value result) :
    (program p).call args s0 = .value (.cons (.value result) .nil,
      {s8 with mem := s8.mem.eraseFrom s0.alloc.nextFreeBlock}) := by
  apply Func.call_of_run
  rw [Func.run_runFrom_eq]
  exact runFrom_of_phases p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ result
    h0 h1 h2 h3 h4 h5 h6 h7 hr

end Agave.Ed25519.SmallOrder.Execution.EqualityPhases

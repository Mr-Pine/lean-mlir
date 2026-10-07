import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorPhases

/-! Exact control-flow composition for the verifier's three-doubling path.
The premises expose the remaining memory/call phases; this theorem does not
claim that those phases or the cofactor layout contract have been discharged. -/
namespace Agave.Ed25519.SmallOrder.Execution.CofactorPhases
open LeanMLIR.RIR Verifier.Execution.PointMulByPow2
set_option maxRecDepth 16000

theorem block_zero (p : Primitives) : (program p).blocks 0 = program.bb0 := rfl
theorem block_one (p : Primitives) : (program p).blocks 1 = program.bb1 := rfl
theorem block_two (p : Primitives) : (program p).blocks 2 = program.bb2 p := rfl

theorem entry_exit : program.bb0.exit =
    .condBr (%15) ⟨2, .nil⟩ ⟨1, .nil⟩ := rfl
theorem setup_exit : program.bb1.exit = .br ⟨3, .cons (%4) .nil⟩ := rfl
theorem return_exit (p : Primitives) : (program.bb2 p).exit = .ret .nil := rfl
theorem params_one : program.blockParams 1 = .nil := rfl

/-- Compose entry, setup, exactly two loop iterations, and the separate final
conversion. Every phase is a slice of the imported body. -/
theorem runFrom_of_phases (p : Primitives)
    (E0 E1 E2 F1 F2 E3 : Env program.Γ)
    (s0 s1 s2 t1 t2 s3 : GlobalState)
    (h0 : List.foldlM Instr.run E0 program.bb0.body s0 = .value (E1, s1))
    (hbranch : E1.read (%15) = .value 0#1)
    (h1 : List.foldlM Instr.run E1 program.bb1.body s1 = .value (E2, s2))
    (hzero : E2.read (%4) = .value 0#32)
    (h2 : List.foldlM Instr.run (E2[%27 := .value 0#32]) (loopPrefix p) s2 =
      .value (F1, t1))
    (hnext1 : F1.read (%28) = .value 1#32)
    (hlimit1 : F1.read (%14) = .value 2#32)
    (h3 : List.foldlM Instr.run (F1[%29 := .value 0#1, %27 := .value 1#32])
      (loopPrefix p) t1 = .value (F2, t2))
    (hnext2 : F2.read (%28) = .value 2#32)
    (hlimit2 : F2.read (%14) = .value 2#32)
    (h4 : List.foldlM Instr.run (F2[%29 := .value 1#1]) (program.bb2 p).body t2 =
      .value (E3, s3)) :
    (program p).runFrom E0 0 s0 = .value (.nil, s3) := by
  have b0 : program.bb0.run program.blockParams E0 s0 =
      .value ((E1, .inr 1), s1) := by
    simp [BasicBlock.run, EffectM.bind_eq, h0, entry_exit, Exit.run,
      hbranch, Jump.run, Regs.read_nil, Env.writeMany_nil, params_one]
  have b1 : program.bb1.run program.blockParams E1 s1 =
      .value ((E2[%27 := .value 0#32], .inr 3), s2) := by
    simp [BasicBlock.run, EffectM.bind_eq, h1, setup_exit, Exit.run,
      Jump.run, Regs.read_cons, Regs.read_nil, hzero, params_three,
      Env.writeMany_cons, Env.writeMany_nil]
  have b2 : (program.bb2 p).run program.blockParams
      (F2[%29 := .value 1#1]) t2 = .value ((E3, .inl .nil), s3) := by
    simp [BasicBlock.run, EffectM.bind_eq, h4, return_exit, Exit.run, Regs.read_nil]
  rw [Func.runFrom_eq, block_zero, b0]
  change (program p).runFrom E1 1 s1 = _
  rw [Func.runFrom_eq, block_one, b1]
  change (program p).runFrom (E2[%27 := .value 0#32]) 3 s2 = _
  rw [first_loop_edge p _ _ _ _ h2 hnext1 hlimit1,
    second_loop_edge p _ _ _ _ h3 hnext2 hlimit2]
  rw [Func.runFrom_eq, block_two, b2]
  rfl

/-- The original function call also reclaims all private allocations at its
entry mark. The explicit phase obligations remain visible in the statement. -/
theorem call_of_phases (p : Primitives) (args : Vals program.Γ.args)
    (E1 E2 F1 F2 E3 : Env program.Γ)
    (s0 s1 s2 t1 t2 s3 : GlobalState)
    (h0 : List.foldlM Instr.run (Env.init args.get) program.bb0.body s0 =
      .value (E1, s1))
    (hbranch : E1.read (%15) = .value 0#1)
    (h1 : List.foldlM Instr.run E1 program.bb1.body s1 = .value (E2, s2))
    (hzero : E2.read (%4) = .value 0#32)
    (h2 : List.foldlM Instr.run (E2[%27 := .value 0#32]) (loopPrefix p) s2 =
      .value (F1, t1))
    (hnext1 : F1.read (%28) = .value 1#32)
    (hlimit1 : F1.read (%14) = .value 2#32)
    (h3 : List.foldlM Instr.run (F1[%29 := .value 0#1, %27 := .value 1#32])
      (loopPrefix p) t1 = .value (F2, t2))
    (hnext2 : F2.read (%28) = .value 2#32)
    (hlimit2 : F2.read (%14) = .value 2#32)
    (h4 : List.foldlM Instr.run (F2[%29 := .value 1#1]) (program.bb2 p).body t2 =
      .value (E3, s3)) :
    (program p).call args s0 =
      .value (.nil, {s3 with mem := s3.mem.eraseFrom s0.alloc.nextFreeBlock}) := by
  apply Func.call_of_run
  rw [Func.run_runFrom_eq]
  exact runFrom_of_phases p _ _ _ _ _ _ _ _ _ _ _ _ h0 hbranch h1 hzero
    h2 hnext1 hlimit1 h3 hnext2 hlimit2 h4

end Agave.Ed25519.SmallOrder.Execution.CofactorPhases

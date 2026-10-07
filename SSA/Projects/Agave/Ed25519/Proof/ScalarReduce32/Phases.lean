import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Program
import SSA.Projects.RIR.Run.Tactic

/-! Exact instruction slices of the one-block imported reducer. Every instruction
appears once, in source order. The phase-composition theorem executes the original
function; it does not replace it with separately written arithmetic code. -/
namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000

abbrev constants := program.entry.body.take 62
abbrev allocations := (program.entry.body.drop 62).take 33
abbrev unpack := (program.entry.body.drop 95).take 108
abbrev multiplication := (program.entry.body.drop 203).take 69
abbrev montgomery := (program.entry.body.drop 272).take 86
abbrev subtract := (program.entry.body.drop 358).take 47
abbrev pack := (program.entry.body.drop 405).take 65
abbrev stores := (program.entry.body.drop 470).take 63
abbrev cleanup := program.entry.body.drop 533

theorem body_length : program.entry.body.length = 622 := by decide +kernel

theorem body_decomposition : program.entry.body =
    constants ++ allocations ++ unpack ++ multiplication ++ montgomery ++
      subtract ++ pack ++ stores ++ cleanup := by rfl

theorem entry_exit : program.entry.exit = .ret .nil := rfl

/-- Per-phase execution facts compose to execution of the actual imported CFG.
The arithmetic phases and cleanup have not been assumed as global axioms. -/
theorem runFrom_of_phases
    (E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 : Env program.Γ)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : GlobalState)
    (h0 : List.foldlM Instr.run E0 constants s0 = .value (E1, s1))
    (h1 : List.foldlM Instr.run E1 allocations s1 = .value (E2, s2))
    (h2 : List.foldlM Instr.run E2 unpack s2 = .value (E3, s3))
    (h3 : List.foldlM Instr.run E3 multiplication s3 = .value (E4, s4))
    (h4 : List.foldlM Instr.run E4 montgomery s4 = .value (E5, s5))
    (h5 : List.foldlM Instr.run E5 subtract s5 = .value (E6, s6))
    (h6 : List.foldlM Instr.run E6 pack s6 = .value (E7, s7))
    (h7 : List.foldlM Instr.run E7 stores s7 = .value (E8, s8))
    (h8 : List.foldlM Instr.run E8 cleanup s8 = .value (E9, s9)) :
    program.runFrom E0 0 s0 = .value (.nil, s9) := by
  have hbody : program.entry.run program.blockParams E0 s0 =
      .value ((E9, .inl .nil), s9) := by
    simp only [BasicBlock.run, body_decomposition, List.foldlM_append,
      EffectM.bind_eq, h0, h1, h2, h3, h4, h5, h6, h7, h8,
      PoisonOr.value_bind, entry_exit, Exit.run, Regs.read_nil, EffectM.pure_eq]
  rw [Func.runFrom_eq]
  change (do
    let ((E', res), s') ← program.entry.run program.blockParams E0 s0
    Func.continue (func := program) E' res s') = _
  rw [hbody]
  rfl

/-- Source phases start from the actual function arguments and return through
its actual private-frame reclamation. -/
theorem call_of_phases
    (args : Vals program.Γ.args)
    (E1 E2 E3 E4 E5 E6 E7 E8 E9 : Env program.Γ)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : GlobalState)
    (h0 : List.foldlM Instr.run (Env.init args.get) constants s0 = .value (E1, s1))
    (h1 : List.foldlM Instr.run E1 allocations s1 = .value (E2, s2))
    (h2 : List.foldlM Instr.run E2 unpack s2 = .value (E3, s3))
    (h3 : List.foldlM Instr.run E3 multiplication s3 = .value (E4, s4))
    (h4 : List.foldlM Instr.run E4 montgomery s4 = .value (E5, s5))
    (h5 : List.foldlM Instr.run E5 subtract s5 = .value (E6, s6))
    (h6 : List.foldlM Instr.run E6 pack s6 = .value (E7, s7))
    (h7 : List.foldlM Instr.run E7 stores s7 = .value (E8, s8))
    (h8 : List.foldlM Instr.run E8 cleanup s8 = .value (E9, s9)) :
    program.call args s0 =
      .value (.nil, {s9 with mem := s9.mem.eraseFrom s0.alloc.nextFreeBlock}) := by
  apply Func.call_of_run
  rw [Func.run_runFrom_eq]
  exact runFrom_of_phases _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    h0 h1 h2 h3 h4 h5 h6 h7 h8

end Agave.Ed25519.ScalarReduce32.Execution

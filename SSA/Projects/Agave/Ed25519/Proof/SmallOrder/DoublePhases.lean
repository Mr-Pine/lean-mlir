import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.SmallOrderProjectiveDoubleProgram
import SSA.Projects.RIR.Run.Tactic

/-! Exact phases of ProjectivePoint::double. The four exponent-one calls are
separated from allocations, sum preparation, flagged arithmetic, and stores.
The original body returns completed XYZT, before conversion by field products. -/
namespace Agave.Ed25519.SmallOrder.Execution.DoublePhases
open LeanMLIR.RIR Verifier.Execution.SmallOrderProjectiveDouble
set_option maxRecDepth 10000

abbrev prepare (p : Primitives) := ((program.entry p).body.drop 0).take 32
abbrev squareX (p : Primitives) := ((program.entry p).body.drop 32).take 1
abbrev prepareY (p : Primitives) := ((program.entry p).body.drop 33).take 2
abbrev squareY (p : Primitives) := ((program.entry p).body.drop 35).take 1
abbrev prepareZ (p : Primitives) := ((program.entry p).body.drop 36).take 3
abbrev squareZ (p : Primitives) := ((program.entry p).body.drop 39).take 1
abbrev prepareSum (p : Primitives) := ((program.entry p).body.drop 40).take 37
abbrev squareSum (p : Primitives) := ((program.entry p).body.drop 77).take 1
abbrev arithmetic (p : Primitives) := ((program.entry p).body.drop 78).take 112
abbrev stores (p : Primitives) := ((program.entry p).body.drop 190).take 39
abbrev cleanup (p : Primitives) := (program.entry p).body.drop 229

theorem body_decomposition (p : Primitives) : (program.entry p).body =
    prepare p ++ squareX p ++ prepareY p ++ squareY p ++ prepareZ p ++ squareZ p ++ prepareSum p ++ squareSum p ++ arithmetic p ++ stores p ++ cleanup p := rfl

theorem block_zero (p : Primitives) : (program p).blocks 0 = program.entry p := rfl

theorem entry_exit (p : Primitives) : (program.entry p).exit = .ret .nil := rfl

/-- Phase equations establish the actual function execution. In particular,
the arithmetic and memory phases remain separate obligations, while the four
square calls can be discharged by `DoubleSquarePhases`. -/
theorem runFrom_of_phases (p : Primitives)
    (E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 : Env program.Γ)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : GlobalState)
    (h0 : List.foldlM Instr.run E0 (prepare p) s0 = .value (E1, s1))
    (h1 : List.foldlM Instr.run E1 (squareX p) s1 = .value (E2, s2))
    (h2 : List.foldlM Instr.run E2 (prepareY p) s2 = .value (E3, s3))
    (h3 : List.foldlM Instr.run E3 (squareY p) s3 = .value (E4, s4))
    (h4 : List.foldlM Instr.run E4 (prepareZ p) s4 = .value (E5, s5))
    (h5 : List.foldlM Instr.run E5 (squareZ p) s5 = .value (E6, s6))
    (h6 : List.foldlM Instr.run E6 (prepareSum p) s6 = .value (E7, s7))
    (h7 : List.foldlM Instr.run E7 (squareSum p) s7 = .value (E8, s8))
    (h8 : List.foldlM Instr.run E8 (arithmetic p) s8 = .value (E9, s9))
    (h9 : List.foldlM Instr.run E9 (stores p) s9 = .value (E10, s10))
    (h10 : List.foldlM Instr.run E10 (cleanup p) s10 = .value (E11, s11)) :
    (program p).runFrom E0 0 s0 = .value (.nil, s11) := by
  have hbody : (program.entry p).run program.blockParams E0 s0 =
      .value ((E11, .inl .nil), s11) := by
    simp only [BasicBlock.run, body_decomposition, List.foldlM_append,
      EffectM.bind_eq, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
      PoisonOr.value_bind, entry_exit, Exit.run, Regs.read_nil, EffectM.pure_eq]
  rw [Func.runFrom_eq, block_zero, hbody]
  rfl

end Agave.Ed25519.SmallOrder.Execution.DoublePhases

import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.ToBytes
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.InstructionTransport

namespace Agave.Ed25519.SmallOrder.Execution.SerializerSource
open LeanMLIR.RIR
open Agave.Ed25519.Encoding.Decompress.Execution.ToBytes
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

abbrev core := program.entry.body.drop 45
abbrev constants := program.entry.body.take 45

def constantEnv (E : Env program.Γ) : Env program.Γ :=
  E[%0 := 8#64, %1 := 16#64, %2 := 24#64, %3 := 32#64, %4 := 51#64, %5 := 2251799813685247#64, %6 := 19#64, %7 := 1#64, %8 := 2#64, %9 := 3#64, %10 := 4#64, %11 := 40#64, %12 := 5#64, %13 := 48#64, %14 := 7#64, %15 := 6#64, %16 := 13#64, %17 := 21#64, %18 := 9#64, %19 := 29#64, %20 := 10#64, %21 := 37#64, %22 := 11#64, %23 := 45#64, %24 := 12#64, %25 := 14#64, %26 := 18#64, %27 := 15#64, %28 := 26#64, %29 := 34#64, %30 := 17#64, %31 := 42#64, %32 := 50#64, %33 := 20#64, %34 := 23#64, %35 := 22#64, %36 := 31#64, %37 := 39#64, %38 := 47#64, %39 := 25#64, %40 := 27#64, %41 := 28#64, %42 := 36#64, %43 := 30#64, %44 := 44#64]

theorem body_exact : program.entry.body = constants ++ core := rfl

theorem constants_run (E : Env program.Γ) (s : GlobalState) :
    constants.foldlM Instr.run E s = .value (constantEnv E, s) := rfl

theorem core_supported : ∀ i ∈ core, Transport.Supported i := by
  simp (maxSteps := 1000000) [core, program.entry, Transport.Supported]

/-- The existing standalone execution proof, restricted to its arithmetic body.
No canonicalization or safety proof is repeated here. -/
theorem core_run (r a : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 32) (ha : SmallRange s.mem a 40) :
    ∃ F, core.foldlM Instr.run
      (constantEnv (Env.init (program.args (.value r) (.value a)).get)) s =
      .value (F, {s with mem := storeBytes s.mem r (machine (SerialFieldMul.readLimbs s a))}) := by
  have h := program_run r a s hwf hr ha
  rw [Func.run_runFrom_eq, Func.runFrom_eq] at h
  have hblock : program.blocks 0 = program.entry := rfl
  have hexit : program.entry.exit = .ret .nil := rfl
  simp only [hblock, BasicBlock.run, body_exact, List.foldlM_append,
    EffectM.bind_eq, constants_run, PoisonOr.value_bind, hexit, Exit.run,
    Regs.read_nil, EffectM.pure_eq, Func.continue] at h
  cases he : core.foldlM Instr.run
      (constantEnv (Env.init (program.args (.value r) (.value a)).get)) s with
  | poison =>
    simp only [he, PoisonOr.poison_bind] at h
    cases h
  | value fs =>
    have ht : fs.2 = {s with mem := storeBytes s.mem r (machine (SerialFieldMul.readLimbs s a))} := by
      simp only [he, PoisonOr.value_bind] at h
      exact congrArg Prod.snd (PoisonOr.value_inj.mp h)
    exact ⟨fs.1, by cases fs; simpa using ht⟩

end Agave.Ed25519.SmallOrder.Execution.SerializerSource

import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.AppendPrefixControl
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.AppendZero

/-! Connect the argument ABI and real counter stores to the two append paths. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Append
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

def startState (s : GlobalState) (context : Pointer) (size : Word) : GlobalState :=
  {s with mem := (counterMemory s.mem context
    (s.mem.readAt (context.add 208#64) 64) (s.mem.readAt (context.add 216#64) 64) size)}

theorem entry_nonempty (core : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (s : GlobalState) (context data : Pointer) (size : Word)
    (hn : size ≠ 0#64) (hc : SmallRange s.mem context 224) :
    ∃ F : Env program.Γ,
      CommonReady F context ∧
      F.read (%arg1) = .value data ∧
      F.read (%arg2) = .value size ∧
      F.read (%14) = .value (s.mem.readAt (context.add 200#64) 64) ∧
      (s.mem.readAt (context.add 200#64) 64 = 0#64 →
        F.read (%36) = .value data ∧ F.read (%37) = .value size) ∧
      (program core).run (program.args (.value context) (.value data) (.value size)) s =
        (program core).runFrom F
          (if s.mem.readAt (context.add 200#64) 64 = 0#64 then 6 else 2)
          (startState s context size) := by
  let E := Env.init (program.args (.value context) (.value data) (.value size)).get
  let A := entryEnv E size
  let used := s.mem.readAt (context.add 200#64) 64
  let lo := s.mem.readAt (context.add 208#64) 64
  let hi := s.mem.readAt (context.add 216#64) 64
  let B := counterEnv A context used lo hi size
  let F := if used = 0#64 then B[%36 := .value data, %37 := .value size] else B
  have h0 := entry_block E s size (by rfl) hn
  change program.bb0.run program.blockParams E s = .value ((A, .inr 1), s) at h0
  have hr : CounterReady A context size := by
    constructor <;> simp [A, entryEnv, E, mlir_env, program.args, Env.init, Vals.get]
  have hb := counter_body A s context used lo hi size hr hc rfl rfl rfl
  change List.foldlM Instr.run A program.bb1.body s =
    .value (B, startState s context size) at hb
  have h1 : program.bb1.run program.blockParams A s =
      .value ((F, .inr (if used = 0#64 then 6 else 2)), startState s context size) := by
    simp only [BasicBlock.run, EffectM.bind_eq, hb, PoisonOr.value_bind]
    by_cases hz : used = 0#64 <;>
      simp [program.bb1, F, B, counterEnv, A, entryEnv, E, program.args, Env.init, Vals.get,
        Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons,
        Env.writeMany_nil, EffectM.pure_eq, mlir_env, mlir_effect, hz, ofBool_eq_one_iff]
  refine ⟨F, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hz : used = 0#64 <;> constructor <;>
      simp [F, B, counterEnv, A, entryEnv, E, program.args, Env.init, Vals.get, mlir_env, hz]
  · by_cases hz : used = 0#64 <;>
      simp [F, B, counterEnv, A, entryEnv, E, program.args, Env.init, Vals.get, mlir_env, hz]
  · by_cases hz : used = 0#64 <;>
      simp [F, B, counterEnv, A, entryEnv, E, program.args, Env.init, Vals.get, mlir_env, hz]
  · by_cases hz : used = 0#64 <;>
      simp [F, B, counterEnv, A, entryEnv, E, program.args, Env.init, Vals.get, mlir_env, hz, used]
  · intro hz
    have hz' : used = 0#64 := hz
    simp [F, hz', mlir_env]
  · rw [Func.run_runFrom_eq]
    change (program core).runFrom E 0 s = _
    rw [next_block core 0 1 E A s s h0,
      next_block core 1 _ A F s (startState s context size) h1]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Append

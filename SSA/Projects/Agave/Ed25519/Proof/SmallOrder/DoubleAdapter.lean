import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.Linked
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.DoubleSquareCall

/-! Relate the exact raw-callee import to the previously imported serial
projective-double body. The adapter is eliminated only for an actual RIR call,
whose private frame is already reclaimed at the same entry allocation mark. -/
namespace Agave.Ed25519.SmallOrder.Execution
open LeanMLIR.RIR
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

private theorem eraseFrom_idempotent (m : MemoryState) (n : Nat) :
    (m.eraseFrom n).eraseFrom n = m.eraseFrom n := by
  apply MemoryState.ext
  apply Std.ExtHashMap.ext_getElem?
  intro id
  simp only [MemoryState.eraseFrom, Std.ExtHashMap.getElem?_filter']
  cases m.mem[id]? <;> by_cases h : id.id < n <;> simp [h]

private theorem adapter_run (f : SerialPoint.Pow2k)
    (a b : PoisonOr Pointer) (k : PoisonOr (BitVec 32)) (s : GlobalState) :
    (SerialPoint.pow2kFunc f).run (.cons a (.cons b (.cons k .nil))) s =
      f (.cons a (.cons b (.cons k .nil))) s := by
  rw [Func.run_runFrom_eq, Func.runFrom_eq]
  simp only [SerialPoint.pow2kFunc, BasicBlock.run, List.foldlM_cons,
    List.foldlM_nil, Instr.run, Regs.read_cons, Regs.read_nil, Env.read_init_arg,
    Vals.get, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  cases h : f (.cons a (.cons b (.cons k .nil))) s with
  | poison => simp [h, Exit.run, Func.continue]
  | value v =>
    obtain ⟨ret, t⟩ := v
    cases ret
    simp [h, Env.writeMany_nil, Exit.run, Regs.read_nil, Func.continue]

/-- A wrapper around this actual imported callee has exactly the same effect,
including poison and private-frame erasure; no success/WF premise is needed. -/
theorem square_adapter_call :
    (SerialPoint.pow2kFunc Encoding.Decompress.Execution.Pow2k.program.call).call =
      Encoding.Decompress.Execution.Pow2k.program.call := by
  funext args s
  cases args with
  | cons a args =>
    cases args with
    | cons b args =>
      cases args with
      | cons k args =>
        cases args
        simp only [Func.call_eq_run_bind, adapter_run]
        cases h : Encoding.Decompress.Execution.Pow2k.program.run
            (.cons a (.cons b (.cons k .nil))) s with
        | poison => rfl
        | value v => simp [eraseFrom_idempotent]


/-- Literal GEP substitution in the older importer produces the same checked
RIR instructions as the direct importer after its ordinary constant folding. -/
theorem projective_double_adapter_program :
    Verifier.Execution.SmallOrderProjectiveDouble.program
      ⟨(SerialPoint.pow2kFunc Encoding.Decompress.Execution.Pow2k.program.call).call⟩ =
      SerialPoint.double Encoding.Decompress.Execution.Pow2k.program.call := rfl

/-- Exact program equality transfers any proved execution theorem about the
older serial body to the direct imported small-order helper. -/
theorem projective_double_program :
    Verifier.Execution.SmallOrderProjectiveDouble.program doublePrimitives =
      SerialPoint.double Encoding.Decompress.Execution.Pow2k.program.call := by
  rw [← projective_double_adapter_program, square_adapter_call]
  rfl

end Agave.Ed25519.SmallOrder.Execution

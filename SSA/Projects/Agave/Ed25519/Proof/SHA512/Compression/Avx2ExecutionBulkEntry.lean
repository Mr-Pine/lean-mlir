import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionEntry

/-! Count-independent execution of the original allocation and parity branch. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

/-- The source tests the low bit before selecting the odd-block prologue. -/
def bulkParity (count : BitVec 64) : BitVec 64 := count &&& 1#64

def bulkEntryEnv (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (count : BitVec 64) : Env program.Γ :=
  (entryConstantsEnv g E)[%81 := .value mem.allocaPtr,
    %82 := .value (mem.alloca 128).allocaPtr,
    %83 := .value ((mem.alloca 128).alloca 640).allocaPtr,
    %84 := .value (bulkParity count),
    %85 := .value (BitVec.ofBool (bulkParity count == 0#64))]

private theorem bulk_modifyGet_apply (f : GlobalState → α × GlobalState) (s : GlobalState) :
    (modifyGet f : EffectM α) s = .value (f s) := rfl

private theorem bulk_entry_allocations_raw (g : Globals) (E : Env program.Γ)
    (mem : GlobalState) (count : BitVec 64)
    (hc : E.read (%arg2) = .value count)
    (h1 : E.read (%1) = .value 1#64) (h0 : E.read (%2) = .value 0#64) :
    List.foldlM Instr.run E ((program.bb0 g).body.drop 81) mem =
      .value (E[%81 := .value mem.allocaPtr,
        %82 := .value (mem.alloca 128).allocaPtr,
        %83 := .value ((mem.alloca 128).alloca 640).allocaPtr,
        %84 := .value (bulkParity count),
        %85 := .value (BitVec.ofBool (bulkParity count == 0#64))], entryState mem) := by
  change E.args 2 = .value count at hc
  simp [program.bb0, entryState, bulkParity, List.foldlM_cons, List.foldlM_nil,
    Instr.run, bulk_modifyGet_apply, Operation.and, Operation.icmp,
    BinOp.compute, EffectM.bind_eq, hc, h1, h0, mlir_env, mlir_effect]

/-- All three original allocations occur even for an empty input slice. -/
theorem bulk_entry_body (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (count : BitVec 64) (hc : E.read (%arg2) = .value count) :
    List.foldlM Instr.run E (program.bb0 g).body mem =
      .value (bulkEntryEnv g E mem count, entryState mem) := by
  have hcut : (program.bb0 g).body =
      (program.bb0 g).body.take 81 ++ (program.bb0 g).body.drop 81 := by rfl
  rw [hcut, List.foldlM_append]
  simp only [EffectM.bind_eq, entry_constants, PoisonOr.value_bind]
  apply bulk_entry_allocations_raw
  · simpa [entryConstantsEnv, entryConstants0, entryConstants1, entryConstants2, mlir_env] using hc
  · simp [entryConstantsEnv, entryConstants0, entryConstants1, entryConstants2, mlir_env]
  · simp [entryConstantsEnv, entryConstants0, entryConstants1, entryConstants2, mlir_env]

/-- Even counts enter the pair-loop test with zero blocks consumed. -/
theorem bulk_entry_even (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (count : BitVec 64) (hc : E.read (%arg2) = .value count)
    (heven : bulkParity count = 0#64) :
    (program.bb0 g).run program.blockParams E mem =
      .value (((bulkEntryEnv g E mem count)[%86 := .value 0#64], .inr 1), entryState mem) := by
  simp only [BasicBlock.run, EffectM.bind_eq, bulk_entry_body g E mem count hc,
    PoisonOr.value_bind]
  simp [program.bb0, bulkEntryEnv, Exit.run, Jump.run, heven,
    feedForward_params1, Regs.read_cons, Regs.read_nil, Env.writeMany_cons,
    Env.writeMany_nil, entryConstantsEnv, entryConstants0, entryConstants1, entryConstants2,
    EffectM.pure_eq, mlir_env, mlir_effect]

/-- Odd counts execute exactly the established one-block prologue environment. -/
theorem bulk_entry_odd (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (count : BitVec 64) (hc : E.read (%arg2) = .value count)
    (hodd : bulkParity count = 1#64) :
    (program.bb0 g).run program.blockParams E mem =
      .value ((entryEnv g E mem, .inr 2), entryState mem) := by
  simp only [BasicBlock.run, EffectM.bind_eq, bulk_entry_body g E mem count hc,
    PoisonOr.value_bind]
  simp [program.bb0, bulkEntryEnv, entryEnv, Exit.run, Jump.run, hodd,
    Regs.read_nil, Env.writeMany_nil, EffectM.pure_eq, mlir_env, mlir_effect]

/-- Allocating and testing parity cannot alter ABI arguments. -/
theorem bulkEntryEnv_frame (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (count : BitVec 64) : RegFrame 0 85 E (bulkEntryEnv g E mem count) := by
  unfold bulkEntryEnv entryConstantsEnv entryConstants2 entryConstants1 entryConstants0
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

end Agave.Ed25519.SHA512.Execution.Avx2

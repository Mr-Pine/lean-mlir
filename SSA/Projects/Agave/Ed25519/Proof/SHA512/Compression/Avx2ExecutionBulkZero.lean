import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkEntry
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionReturn
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionEntryMemory

/-! The original empty-input path, including allocations, zero fill, and cleanup. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

/-- The loop test is meaningful independently of the odd-block specialization. -/
structure BulkTestReady (E : Env program.Γ) (buffer : Pointer)
    (count consumed : BitVec 64) : Prop where
  count : E.read (%arg2) = .value count
  consumed : E.read (%86) = .value consumed
  bufferPtr : E.read (%82) = .value buffer
  offset : E.read (%47) = .value 128#64
  byteZero : E.read (%48) = .value 0#8
  length : E.read (%49) = .value 512#64
  one : E.read (%1) = .value 1#64
  zero : E.read (%2) = .value 0#64

/-- Equal total and consumed counts make the saturating subtraction exactly
zero. The emitted memset still occurs before this decision. -/
theorem bulk_test_done (E : Env program.Γ) (mem : GlobalState) (buffer : Pointer)
    (count : BitVec 64) (h : BulkTestReady E buffer count count)
    (hlive : SmallRange mem.mem buffer 640) :
    program.bb1.run program.blockParams E mem =
      .value ((returnEnv E buffer, .inr 18), returnState mem buffer) := by
  have hfit : Fits mem.mem (buffer.add 128#64) 4096 :=
    hlive.fits_add (k := 128) (count := 512) (by decide)
  have hgep := hlive.gep (k := 128) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  rcases h with ⟨hc, hi, hb, ho, hz, hl, h1, h0⟩
  change E.args 2 = .value count at hc
  simp [BasicBlock.run, program.bb1, List.foldlM_cons, List.foldlM_nil,
    Instr.run, BinOp.compute, Operation.usubSat, Operation.memset,
    returnEnv, returnState, hc, hi, hb, hz, hl, h1, h0, hfit, hgep,
    Operation.lshr, Operation.sub, Operation.icmp, BitVec.ssubOverflow,
    Exit.run, Jump.run, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem bulk_test_done_runFrom (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (buffer : Pointer) (count : BitVec 64) (h : BulkTestReady E buffer count count)
    (hlive : SmallRange mem.mem buffer 640) :
    (program g).runFrom E 1 mem = .value (.nil, returnState mem buffer) := by
  rw [Func.runFrom_eq]
  change (program.bb1.run program.blockParams E mem >>= _) = _
  rw [bulk_test_done E mem buffer count h hlive]
  exact return_end_runFrom g _ _

theorem bulk_test_done_evalFrom (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (buffer : Pointer) (count : BitVec 64) (h : BulkTestReady E buffer count count)
    (hlive : SmallRange mem.mem buffer 640) :
    (program g).evalFrom 2 E 1 mem = .value (some .nil, returnState mem buffer) := by
  rw [Func.evalFrom]
  change (program.bb1.run program.blockParams E mem >>= _) = _
  rw [bulk_test_done E mem buffer count h hlive]
  simp only [PoisonOr.value_bind]
  change (program g).evalFrom 1 (returnEnv E buffer) 18 (returnState mem buffer) = _
  rw [Func.evalFrom]
  simp only [EffectM.bind_eq]
  change (program.bb18.run program.blockParams (returnEnv E buffer)
    (returnState mem buffer) >>= _) = _
  rw [return_end_block]
  rfl

private theorem bulk_zero_ready (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (hc : E.read (%arg2) = .value 0#64) :
    BulkTestReady ((bulkEntryEnv g E mem 0#64)[%86 := .value 0#64])
      (mem.alloca 128).allocaPtr 0#64 0#64 := by
  change E.args 2 = .value 0#64 at hc
  constructor <;> simp [bulkEntryEnv, entryConstantsEnv, entryConstants0,
    entryConstants1, entryConstants2, mlir_env, hc]

/-- Three concrete blocks suffice for zero input: bb0, bb1, bb18. -/
theorem bulk_zero_evalFrom (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (hwf : mem.WF) (hc : E.read (%arg2) = .value 0#64) :
    (program g).evalFrom 3 E 0 mem = .value (some .nil,
      returnState (entryState mem) (mem.alloca 128).allocaPtr) := by
  rw [Func.evalFrom]
  change ((program.bb0 g).run program.blockParams E mem >>= _) = _
  rw [bulk_entry_even g E mem 0#64 hc (by decide)]
  exact bulk_test_done_evalFrom g _ _ _ _ (bulk_zero_ready g E mem hc)
    (entry_cache_live mem hwf)

theorem bulk_zero_runFrom (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (hwf : mem.WF) (hc : E.read (%arg2) = .value 0#64) :
    (program g).runFrom E 0 mem = .value (.nil,
      returnState (entryState mem) (mem.alloca 128).allocaPtr) := by
  rw [Func.runFrom_eq]
  change ((program.bb0 g).run program.blockParams E mem >>= _) = _
  rw [bulk_entry_even g E mem 0#64 hc (by decide)]
  exact bulk_test_done_runFrom g _ _ _ _ (bulk_zero_ready g E mem hc)
    (entry_cache_live mem hwf)

/-- Cleanup removes the zero-fill destination and the two other fresh slots;
all caller memory is therefore exactly unchanged at zero count. -/
theorem bulk_zero_call (g : Globals) (mem : GlobalState) (chain data : Pointer)
    (hwf : mem.WF) :
    (program g).call (.cons (.value chain) (.cons (.value data) (.cons (.value 0#64) .nil)))
      mem = .value (.nil, { alloc := ⟨mem.alloc.nextFreeBlock + 3⟩, mem := mem.mem }) := by
  let args : Vals program.Γ.args :=
    .cons (.value chain) (.cons (.value data) (.cons (.value 0#64) .nil))
  have hr : (program g).run args mem = .value (.nil,
      returnState (entryState mem) (mem.alloca 128).allocaPtr) := by
    rw [Func.run_runFrom_eq]
    exact bulk_zero_runFrom g (Env.init args.get) mem hwf rfl
  have hc := Func.call_of_run hr
  rw [returnState_erase (entryState mem) (mem.alloca 128).allocaPtr mem.alloc.nextFreeBlock
      (by simp [GlobalState.allocaPtr, GlobalState.alloca]), entryState_frame mem hwf] at hc
  simpa only [args, returnState, entryState, GlobalState.alloca] using hc

end Agave.Ed25519.SHA512.Execution.Avx2

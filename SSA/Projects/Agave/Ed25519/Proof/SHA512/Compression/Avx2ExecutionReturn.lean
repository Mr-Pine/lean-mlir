import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2Program
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-! The exact one-block outer-loop exit, including the final scratch memset. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

structure ReturnReady (E : Env program.Γ) (buffer : Pointer) : Prop where
  count : E.read (%arg2) = .value 1#64
  current : E.read (%86) = .value 1#64
  bufferPtr : E.read (%82) = .value buffer
  offset : E.read (%47) = .value 128#64
  byteZero : E.read (%48) = .value 0#8
  length : E.read (%49) = .value 512#64
  one : E.read (%1) = .value 1#64
  zero : E.read (%2) = .value 0#64

def returnState (mem : GlobalState) (buffer : Pointer) : GlobalState :=
  { mem with mem := mem.mem.storeAt (buffer.add 128#64) (0#4096) }

def returnEnv (E : Env program.Γ) (buffer : Pointer) : Env program.Γ :=
  E[%87 := .value (buffer.add 128#64), %88 := .value 0#64,
    %89 := .value 0#64, %90 := .value 0#64, %91 := .value 1#1]

@[simp] theorem return_params18 : program.blockParams 18 = .nil := rfl

theorem return_block (E : Env program.Γ) (mem : GlobalState) (buffer : Pointer)
    (h : ReturnReady E buffer) (hlive : SmallRange mem.mem buffer 640) :
    program.bb1.run program.blockParams E mem =
      .value ((returnEnv E buffer, .inr 18), returnState mem buffer) := by
  have hfit : Fits mem.mem (buffer.add 128#64) 4096 :=
    hlive.fits_add (k := 128) (count := 512) (by decide)
  have hgep := hlive.gep (k := 128) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  rcases h with ⟨hc, hi, hb, ho, hz, hl, h1, h0⟩
  change E.args 2 = .value 1#64 at hc
  simp [BasicBlock.run, program.bb1, List.foldlM_cons, List.foldlM_nil,
    Instr.run, BinOp.compute, Operation.usubSat, Operation.memset,
    returnEnv, returnState, hc, hi, hb, hz, hl, h1, h0, hfit, hgep,
    Operation.lshr, Operation.sub, Operation.icmp, BitVec.ssubOverflow,
    Exit.run, Jump.run, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem return_end_block (E : Env program.Γ) (mem : GlobalState) :
    program.bb18.run program.blockParams E mem = .value ((E, .inl .nil), mem) := by
  simp [BasicBlock.run, program.bb18, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Exit.run, Regs.read_nil, EffectM.bind_eq, EffectM.pure_eq, mlir_effect]

theorem return_end_runFrom (g : Globals) (E : Env program.Γ) (mem : GlobalState) :
    (program g).runFrom E 18 mem = .value (.nil, mem) := by
  rw [Func.runFrom_eq]
  change (program.bb18.run program.blockParams E mem >>= _) = _
  rw [return_end_block]
  rfl

theorem return_runFrom (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (buffer : Pointer) (h : ReturnReady E buffer) (hlive : SmallRange mem.mem buffer 640) :
    (program g).runFrom E 1 mem = .value (.nil, returnState mem buffer) := by
  rw [Func.runFrom_eq]
  change (program.bb1.run program.blockParams E mem >>= _) = _
  rw [return_block E mem buffer h hlive]
  exact return_end_runFrom g _ _

/-- The final outer-loop test composes with the actual return block. -/
theorem return_continuation (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (buffer : Pointer) (h : ReturnReady E buffer) (hlive : SmallRange mem.mem buffer 640) :
    (program g).runFrom E 1 mem =
      (program g).runFrom (returnEnv E buffer) 18 (returnState mem buffer) := by
  rw [return_runFrom g E mem buffer h hlive, return_end_runFrom]

theorem return_evalFrom (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (buffer : Pointer) (h : ReturnReady E buffer) (hlive : SmallRange mem.mem buffer 640) :
    (program g).evalFrom 2 E 1 mem = .value (some .nil, returnState mem buffer) := by
  rw [Func.evalFrom]
  change (program.bb1.run program.blockParams E mem >>= _) = _
  rw [return_block E mem buffer h hlive]
  simp only [PoisonOr.value_bind]
  change (program g).evalFrom 1 (returnEnv E buffer) 18 (returnState mem buffer) = _
  rw [Func.evalFrom]
  simp only [EffectM.bind_eq]
  change (program.bb18.run program.blockParams (returnEnv E buffer)
    (returnState mem buffer) >>= _) = _
  rw [return_end_block]
  rfl

theorem returnState_zero (mem : GlobalState) (buffer : Pointer)
    (hlive : SmallRange mem.mem buffer 640) :
    (returnState mem buffer).mem.readAt (buffer.add 128#64) 4096 = 0#4096 :=
  MemoryState.readAt_storeAt_self
    (hlive.fits_add (k := 128) (count := 512) (by decide)) _

theorem returnState_read_frame (mem : GlobalState) (buffer p : Pointer) (w : Nat)
    (hd : (Range.of (buffer.add 128#64) 4096).Disjoint (Range.of p w)) :
    (returnState mem buffer).mem.readAt p w = mem.mem.readAt p w :=
  MemoryState.readAt_storeAt_disjoint hd _

/-- In particular, the chaining state and caller buffers in other allocations
are untouched by the real final memset. -/
theorem returnState_read_other (mem : GlobalState) (buffer p : Pointer) (w : Nat)
    (h : buffer.id ≠ p.id) :
    (returnState mem buffer).mem.readAt p w = mem.mem.readAt p w :=
  returnState_read_frame mem buffer p w (Range.disjoint_of_id_ne h)

/-- The final zero fill is confined to an allocation removed on return. -/
theorem returnState_erase (mem : GlobalState) (buffer : Pointer) (mark : Nat)
    (hprivate : mark ≤ buffer.id.id) :
    (returnState mem buffer).mem.eraseFrom mark = mem.mem.eraseFrom mark := by
  simp only [returnState, MemoryState.eraseFrom_storeAt]
  exact MemoryState.storeAt_eraseFrom_of_le (p := buffer.add 128#64) hprivate

@[simp] theorem returnState_alloc (mem : GlobalState) (buffer : Pointer) :
    (returnState mem buffer).alloc = mem.alloc := rfl

theorem returnState_live (mem : GlobalState) (buffer p : Pointer) (n : Nat)
    (h : SmallRange mem.mem p n) : SmallRange (returnState mem buffer).mem p n :=
  h.storeAt _ _

theorem returnState_wf (mem : GlobalState) (buffer : Pointer) (h : mem.WF) :
    (returnState mem buffer).WF := h.storeAt

end Agave.Ed25519.SHA512.Execution.Avx2

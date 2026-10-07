import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.Program
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.Arithmetic
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-! Exact first nonempty append block: read the streaming state, update both
bit-count words with carry, and test the pending-byte count. No core call is
made in this block. All register and memory results are specified. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Append
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def counterMemory (m : MemoryState) (context : Pointer) (lo hi size : Word) : MemoryState :=
  (m.storeAt (context.add 208#64) (appendLow lo size)).storeAt
    (context.add 216#64) (appendHigh hi lo size)

structure CounterReady (E : Env program.Γ) (context : Pointer) (size : Word) : Prop where
  context : E.read (%arg0) = .value context
  size : E.read (%arg2) = .value size
  c0 : E.read (%0) = .value 0#64
  c1 : E.read (%1) = .value 128#64
  c2 : E.read (%2) = .value 200#64
  c3 : E.read (%3) = .value 208#64
  c4 : E.read (%4) = .value 216#64
  c5 : E.read (%5) = .value 3#64
  c6 : E.read (%6) = .value 61#64

def counterEnv (E : Env program.Γ) (context : Pointer) (used lo hi size : Word) :
    Env program.Γ :=
  E[%12 := .value (context.add 128#64),
    %13 := .value (context.add 200#64),
    %14 := .value used,
    %15 := .value (context.add 208#64),
    %16 := .value lo,
    %17 := .value (context.add 216#64),
    %18 := .value hi,
    %19 := .value (size <<< 3),
    %20 := .value (appendLow lo size),
    %21 := .value (size >>> 61),
    %22 := .value (hi + (size >>> 61)),
    %23 := .value (BitVec.ofBool ((appendLow lo size).ult lo)),
    %24 := .value (if (appendLow lo size).ult lo then 1#64 else 0#64),
    %25 := .value (appendHigh hi lo size),
    %26 := .value (BitVec.ofBool (used == 0))]

theorem counter_body (E : Env program.Γ) (state : GlobalState) (context : Pointer)
    (used lo hi size : Word) (h : CounterReady E context size)
    (hr : SmallRange state.mem context 224)
    (hu : state.mem.readAt (context.add 200#64) 64 = used)
    (hlo : state.mem.readAt (context.add 208#64) 64 = lo)
    (hhi : state.mem.readAt (context.add 216#64) 64 = hi) :
    List.foldlM Instr.run E program.bb1.body state =
      .value (counterEnv E context used lo hi size,
        {state with mem := counterMemory state.mem context lo hi size}) := by
  have hcontext : E.args 0 = .value context := h.context
  have hsize : E.args 2 = .value size := h.size
  have hg128 := hr.gep (k := 128) (by decide)
  have hg200 := hr.gep (k := 200) (by decide)
  have hg208 := hr.gep (k := 208) (by decide)
  have hg216 := hr.gep (k := 216) (by decide)
  have hf200 := hr.fits_add (k := 200) (count := 8) (by decide)
  have hf208 := hr.fits_add (k := 208) (count := 8) (by decide)
  have hf216 := hr.fits_add (k := 216) (count := 8) (by decide)
  have hfst216 := (hr.storeAt (context.add 208#64) (appendLow lo size)).fits_add
    (k := 216) (count := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hg128 hg200 hg208 hg216
  simp only [appendLow] at hfst216
  have hext (b : Bool) : (BitVec.ofBool b).setWidth 64 = (if b then 1#64 else 0#64) := by
    cases b <;> rfl
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb1, List.foldlM_cons, List.foldlM_nil, Instr.run,
    counterEnv, counterMemory, hcontext, hsize, h.context, h.size, h.c0, h.c1, h.c2, h.c3, h.c4, h.c5, h.c6,
    hg128, hg200, hg208, hg216, hf200, hf208, hf216, hfst216, hu, hlo, hhi,
    Operation.load, Operation.store, Operation.shl, Operation.lshr, Operation.icmp,
    Operation.zext, hadd, hext, appendLow, appendHigh,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    BinOp.compute, UnOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]
  constructor <;> rfl

/-- The source stores represent one 128-bit addition, including wraparound. -/
theorem counter_value (hi lo size : Word) :
    appendHigh hi lo size ++ appendLow lo size =
      (hi ++ lo) + (size.setWidth 128 <<< 3) := append_counter hi lo size

theorem counterMemory_wf (state : GlobalState) (context : Pointer) (lo hi size : Word)
    (hwf : state.WF) :
    ({state with mem := counterMemory state.mem context lo hi size} : GlobalState).WF := by
  simpa only [counterMemory, GlobalState.WF_storeAt] using hwf

theorem counterMemory_other_block (m : MemoryState) (context : Pointer)
    (lo hi size : Word) (id : BlockId) (hne : id ≠ context.id) :
    (counterMemory m context lo hi size)[id]? = m[id]? := by
  have hn (k : BitVec 64) : (⟨id, 0⟩ : Pointer).id ≠ (context.add k).id := hne
  simp only [counterMemory, MemoryState.getElem?_storeAt_ne (hn _)]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Append

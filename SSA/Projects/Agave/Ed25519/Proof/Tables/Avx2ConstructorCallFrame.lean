import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorState
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorReturn
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorStack
import SSA.Projects.Agave.Ed25519.Proof.Verifier.KeyExecutionMemory

namespace Agave.Ed25519.Tables.Avx2Constructor.CallFrame
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open DoubleBase.SerialContracts (WritesOnly)
open Stack
open State (Frame slots)
open Verifier.Execution.Key (erase_get erase_read)
variable {q : Pointer} {id : BlockId}

theorem stack_separate_old (hq : q.id.id < s.alloc.nextFreeBlock) (n : Nat) :
    (pointer s n).id ≠ q.id := by
  intro he
  have hi := congrArg BlockId.id he
  rw [pointer_id] at hi
  omega

theorem stack_get_old (hid : id.id < s.alloc.nextFreeBlock) (n : Nat) :
    (state s n).mem[id]? = s.mem[id]? := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ((state s n).alloca _).mem[id]? = _
      rw [GlobalState.getElem?_alloca (by
        have hn := stack_separate_old (q := ⟨id, 0⟩) hid n
        exact hn.symm), ih]

theorem stack_read_old (hq : q.id.id < s.alloc.nextFreeBlock) (n bits : Nat) :
    (state s n).mem.readAt q bits = s.mem.readAt q bits := by
  simp only [MemoryState.readAt, stack_get_old hq]

private theorem erase_get_new (m : MemoryState) (id : BlockId)
    (h : cutoff ≤ id.id) : (m.eraseFrom cutoff)[id]? = none := by
  simp [MemoryState.eraseFrom, MemoryState.getElem?_eq,
    Std.ExtHashMap.getElem?_filter', show ¬id.id < cutoff by omega]

private theorem erase_read_new (m : MemoryState) (q : Pointer) (bits : Nat)
    (h : cutoff ≤ q.id.id) : (m.eraseFrom cutoff).readAt q bits = 0 := by
  simp only [MemoryState.readAt, erase_get_new m q.id h]

/-- Erasure of precisely this constructor's fresh stack restores the complete
caller allocation shape, including absent allocation ids. -/
theorem caller_writesOnly (s t u : GlobalState) (out : Pointer) (hwf : s.WF)
    (hf : Frame (slots s) (pointer s 8) (state s 9) t)
    (ho : WritesOnly out 1280 t u) :
    WritesOnly out 1280 s {u with mem := u.mem.eraseFrom s.alloc.nextFreeBlock} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro id hi
    exact ho.wellFormed id (Std.ExtHashMap.mem_filter.mp hi).1
  · have hmono : s.alloc.nextFreeBlock ≤ (state s 9).alloc.nextFreeBlock := by
      rw [counter]; omega
    exact hmono.trans (hf.allocationMonotone.trans ho.allocationMonotone)
  · intro id
    by_cases hid : id.id < s.alloc.nextFreeBlock
    · rw [erase_get u.mem id _ hid, ho.allocationShape id, hf.allocationShape id,
        stack_get_old hid]
    · rw [erase_get_new u.mem id (by omega), ← hwf.eraseFrom,
        erase_get_new s.mem id (by omega)]
  · intro q bits hd
    by_cases hq : q.id.id < s.alloc.nextFreeBlock
    · rw [erase_read u.mem q _ bits hq, ho.readFrame q bits hd,
        hf.readFrame q bits (fun i => stack_separate_old hq i.val) (stack_separate_old hq 8),
        stack_read_old hq]
    · rw [erase_read_new u.mem q bits (by omega), ← hwf.eraseFrom,
        erase_read_new s.mem q bits (by omega)]

/-- Convert the stronger allocation-shape certificate to the exact frame
required by the double-base table contract after Func.call erases fresh blocks. -/
theorem caller_frame (s t u : GlobalState) (out : Pointer) (hwf : s.WF)
    (hf : Frame (slots s) (pointer s 8) (state s 9) t)
    (ho : WritesOnly out 1280 t u) :
    DoubleBase.ExecutionAvx2.TableFrame s
      {u with mem := u.mem.eraseFrom s.alloc.nextFreeBlock} out := by
  have h := caller_writesOnly s t u out hwf hf ho
  exact ⟨h.wellFormed, fun _ _ hr => h.smallRange hr, h.readFrame⟩

/-- Erasure preserves every packed source block in an old caller allocation. -/
theorem erase_readBlocks (s t : GlobalState) (q : Pointer)
    (hq : q.id.id < s.alloc.nextFreeBlock) :
    Avx2FieldMul.Execution.readBlocks (t.mem.eraseFrom s.alloc.nextFreeBlock) q =
      Avx2FieldMul.Execution.readBlocks t.mem q := by
  funext i
  simp only [Avx2FieldMul.Execution.readBlocks,
    erase_read t.mem (q.add (BitVec.ofNat 64 (32*i.val))) s.alloc.nextFreeBlock 256
      (by simpa only [Pointer.add_id] using hq)]

theorem erase_packedPoint (s t : GlobalState) (q : Pointer)
    (hq : q.id.id < s.alloc.nextFreeBlock) :
    DoubleBase.ExecutionAvx2.packedPoint (t.mem.eraseFrom s.alloc.nextFreeBlock) q =
      DoubleBase.ExecutionAvx2.packedPoint t.mem q := by
  simp only [DoubleBase.ExecutionAvx2.packedPoint, erase_readBlocks s t q hq]

end Agave.Ed25519.Tables.Avx2Constructor.CallFrame

open Lean in
run_cmd do
  for endpoint in [
      `Agave.Ed25519.Tables.Avx2Constructor.CallFrame.caller_writesOnly,
      `Agave.Ed25519.Tables.Avx2Constructor.CallFrame.caller_frame,
      `Agave.Ed25519.Tables.Avx2Constructor.CallFrame.erase_readBlocks,
      `Agave.Ed25519.Tables.Avx2Constructor.CallFrame.erase_packedPoint] do
    for dependency in (← collectAxioms endpoint) do
      unless [`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{endpoint} depends on forbidden axiom {dependency}"
    logInfo m!"standard-three audit passed: {endpoint}"

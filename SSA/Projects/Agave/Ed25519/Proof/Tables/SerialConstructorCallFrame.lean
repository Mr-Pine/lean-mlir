import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorState
import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorStack
import SSA.Projects.Agave.Ed25519.Proof.Verifier.KeyExecutionMemory

namespace Agave.Ed25519.Tables.SerialConstructorCallFrame
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open DoubleBase.SerialContracts (WritesOnly readField readCached)
open SerialConstructorStack
open SerialConstructorState (Frame)
open Verifier.Execution.Key (erase_get erase_read)
variable {q : Pointer} {id : BlockId}

def slots (s : GlobalState) : Fin 7 → Pointer := fun i => stackPtr s i.val

theorem stack_separate_old (hq : q.id.id < s.alloc.nextFreeBlock) (n : Nat) :
    (stackPtr s n).id ≠ q.id := by
  intro he
  have hi := congrArg BlockId.id he
  rw [stackPtr_id] at hi
  omega

theorem stack_get_old (hid : id.id < s.alloc.nextFreeBlock) (n : Nat) :
    (stack s n).mem[id]? = s.mem[id]? := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ((stack s n).alloca _).mem[id]? = _
      rw [GlobalState.getElem?_alloca (by
        have hn := stack_separate_old (q := ⟨id, 0⟩) hid n
        exact hn.symm), ih]

theorem stack_read_old (hq : q.id.id < s.alloc.nextFreeBlock) (n bits : Nat) :
    (stack s n).mem.readAt q bits = s.mem.readAt q bits := by
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
theorem caller_frame (s t u : GlobalState) (out : Pointer) (hwf : s.WF)
    (hf : Frame (slots s) (stackPtr s 7) (stack s 8) t)
    (ho : WritesOnly out 1280 t u) :
    WritesOnly out 1280 s {u with mem := u.mem.eraseFrom s.alloc.nextFreeBlock} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro id hi
    exact ho.wellFormed id (Std.ExtHashMap.mem_filter.mp hi).1
  · have hmono : s.alloc.nextFreeBlock ≤ (stack s 8).alloc.nextFreeBlock := by
      rw [stack_counter]; omega
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
        hf.readFrame q bits (fun i => stack_separate_old hq i.val) (stack_separate_old hq 7),
        stack_read_old hq]
    · rw [erase_read_new u.mem q bits (by omega), ← hwf.eraseFrom,
        erase_read_new s.mem q bits (by omega)]

theorem erase_cached (s t : GlobalState) (q : Pointer)
    (hq : q.id.id < s.alloc.nextFreeBlock) :
    readCached {t with mem := t.mem.eraseFrom s.alloc.nextFreeBlock} q = readCached t q := by
  apply PointArithmetic.Extended.ext
  all_goals
    dsimp only [readCached]
    unfold readField SerialFieldMul.unsigned SerialFieldMul.readLimbs
    funext i
    rw [erase_read t.mem _ _ _ (by simpa only [Pointer.add_id] using hq)]

end Agave.Ed25519.Tables.SerialConstructorCallFrame

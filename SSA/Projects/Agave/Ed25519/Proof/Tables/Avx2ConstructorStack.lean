import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2Constructor
import SSA.Projects.Agave.Ed25519.Proof.Tables.Memory
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGSlice
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2NAFFrame

/-! The nine real constructor allocations. All preservation and separation
facts refer to the actual pointer assigned to each source stack slot. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Stack
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open Avx2PointAdd.CFG (runSlice)
open DoubleBase.ExecutionAvx2 (RegisterFrame)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def size (i : Nat) : Nat := if i = 8 then 1280 else 160

def state (s : GlobalState) : Nat → GlobalState
  | 0 => s
  | n+1 => (state s n).alloca (size n)

def pointer (s : GlobalState) (i : Nat) : Pointer := (state s i).allocaPtr

theorem wf (h : s.WF) (n : Nat) : (state s n).WF := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.alloca

theorem live (h : s.WF) (hq : Buffer s.mem q bytes) (n : Nat) :
    Buffer (state s n).mem q bytes := by
  induction n with
  | zero => exact hq
  | succ n ih => exact ih.alloca_existing (wf h n) _

theorem read_existing (h : s.WF) (hq : Buffer s.mem q bytes) (n bits : Nat) :
    (state s n).mem.readAt q bits = s.mem.readAt q bits := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((state s n).alloca _).mem.readAt q bits = _
    rw [MemoryState.readAt_alloca (wf h n) (live h hq n).fits, ih]

theorem buffer (h : s.WF) (i n : Nat) (hi : i < n) :
    Buffer (state s n).mem (pointer s i) (size i) := by
  have hsize : size i < 2^63 := by unfold size; split <;> decide
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : i = n
    · subst i; exact Buffer.alloca _ _ hsize
    · exact (ih (by omega)).alloca_existing (wf h n) _

theorem separate_caller (h : s.WF) (hq : Buffer s.mem q bytes) (n : Nat) :
    (pointer s n).id ≠ q.id :=
  (GlobalState.ne_allocaPtr_of_fits (wf h n) (live h hq n).fits).symm

theorem counter (s : GlobalState) (n : Nat) :
    (state s n).alloc.nextFreeBlock = s.alloc.nextFreeBlock+n := by
  induction n with
  | zero => simp [state]
  | succ n ih => simp only [state, GlobalState.alloca, ih, Nat.add_assoc]

theorem pointer_id (s : GlobalState) (i : Nat) :
    (pointer s i).id.id = s.alloc.nextFreeBlock+i := counter s i

theorem separate (s : GlobalState) (i j : Nat) (h : i ≠ j) :
    (pointer s i).id ≠ (pointer s j).id := by
  intro he
  have hv := congrArg BlockId.id he
  rw [pointer_id, pointer_id] at hv
  omega

def result (E : ⟪kernel.Γ⟫) (s : GlobalState) : ⟪kernel.Γ⟫ :=
  E[%352 := .value (pointer s 0), %353 := .value (pointer s 1),
    %354 := .value (pointer s 2), %355 := .value (pointer s 3),
    %356 := .value (pointer s 4), %357 := .value (pointer s 5),
    %358 := .value (pointer s 6), %359 := .value (pointer s 7),
    %360 := .value (pointer s 8)]

theorem register_frame (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    RegisterFrame 352 361 E (result E s) := by
  unfold result
  iterate 9 apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

private theorem modifyGet_run {α : Type} (f : GlobalState → α × GlobalState)
    (s : GlobalState) : (modifyGet f : EffectM α) s = .value (f s) := rfl

/-- Execute only the original nine allocation instructions. -/
theorem run (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState)
    (hcount : E.read (%0) = .value 1#32) :
    runSlice (kernel.bb0 p) E 352 9 s = .value (result E s, state s 9) := by
  simp [runSlice, kernel.bb0, result, state, size, pointer,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Ty.wrap, EffectM.bind_eq,
    EffectM.pure_eq, PoisonOr.value_bind, modifyGet_run, mlir_env, hcount]

end Agave.Ed25519.Tables.Avx2Constructor.Stack

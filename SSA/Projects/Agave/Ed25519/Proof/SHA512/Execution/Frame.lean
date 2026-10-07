import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Contracts
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionMemory

/-! Allocation and frame facts for the finalizer's 70 stack allocations.
These are independent of the external primitive implementations. -/

namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Challenge

variable {s : GlobalState} {m : MemoryState} {p : Pointer} {n i mark : Nat}

/-- Allocate the listed stack slots in the emitted order. -/
def allocateSlots (s : GlobalState) : List Nat → GlobalState
  | [] => s
  | bytes :: rest => allocateSlots (s.alloca bytes) rest

/-- Four block buffers, the serialized digest, a private context, and the
sixty-four one-byte slots used by the extracted zeroization sequence. -/
def slotSizes : List Nat := [128, 128, 128, 128, 64, 208] ++ List.replicate 64 1

@[simp] theorem slotSizes_length : slotSizes.length = 70 := by simp [slotSizes]

theorem allocateSlots_append (s : GlobalState) (xs ys : List Nat) :
    allocateSlots s (xs ++ ys) = allocateSlots (allocateSlots s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons bytes rest ih => exact ih (s.alloca bytes)

theorem allocateSlots_wf (sizes : List Nat) (hwf : s.WF) :
    (allocateSlots s sizes).WF := by
  induction sizes generalizing s with
  | nil => exact hwf
  | cons bytes rest ih => exact ih hwf.alloca

@[simp] theorem allocateSlots_counter (sizes : List Nat) (s : GlobalState) :
    (allocateSlots s sizes).alloc.nextFreeBlock = s.alloc.nextFreeBlock + sizes.length := by
  induction sizes generalizing s with
  | nil => simp [allocateSlots]
  | cons bytes rest ih =>
    simp only [allocateSlots, ih, GlobalState.alloca, List.length_cons]
    omega

theorem allocateSlots_live (sizes : List Nat) (hwf : s.WF)
    (hr : SmallRange s.mem p n) : SmallRange (allocateSlots s sizes).mem p n := by
  induction sizes generalizing s with
  | nil => exact hr
  | cons bytes rest ih => exact ih hwf.alloca (smallRange_alloca hwf hr)

/-- Each allocated slot remains live after every later allocation. -/
theorem allocateSlots_slot_live (sizes : List Nat) (hwf : s.WF)
    (hi : i < sizes.length) (hsmall : sizes[i] < 2 ^ 63) :
    SmallRange (allocateSlots s sizes).mem
      (allocateSlots s (sizes.take i)).allocaPtr sizes[i] := by
  have hsplit : sizes = sizes.take i ++ sizes[i] :: sizes.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have heq : allocateSlots s sizes =
      allocateSlots ((allocateSlots s (sizes.take i)).alloca sizes[i])
        (sizes.drop (i + 1)) := by
    calc
      _ = allocateSlots s (sizes.take i ++ sizes[i] :: sizes.drop (i + 1)) :=
        congrArg (allocateSlots s) hsplit
      _ = _ := allocateSlots_append _ _ _
  rw [heq]
  exact allocateSlots_live _ (allocateSlots_wf _ hwf).alloca
    (smallRange_alloca_self _ _ hsmall)

theorem allocateSlots_read (sizes : List Nat) (hwf : s.WF)
    (hr : SmallRange s.mem p n) (width : Nat) :
    (allocateSlots s sizes).mem.readAt p width = s.mem.readAt p width := by
  induction sizes generalizing s with
  | nil => rfl
  | cons bytes rest ih =>
    rw [allocateSlots, ih hwf.alloca (smallRange_alloca hwf hr),
      MemoryState.readAt_alloca hwf hr.fits]

theorem allocateSlots_frame_le (sizes : List Nat) (s : GlobalState)
    (hmark : mark ≤ s.alloc.nextFreeBlock) :
    (allocateSlots s sizes).mem.eraseFrom mark = s.mem.eraseFrom mark := by
  induction sizes generalizing s with
  | nil => rfl
  | cons bytes rest ih =>
    rw [allocateSlots, ih _ (by simpa [GlobalState.alloca] using Nat.le_succ_of_le hmark),
      GlobalState.eraseFrom_alloca_of_le hmark]

theorem allocateSlots_frame (sizes : List Nat) (s : GlobalState) (hwf : s.WF) :
    (allocateSlots s sizes).mem.eraseFrom s.alloc.nextFreeBlock = s.mem := by
  rw [allocateSlots_frame_le sizes s (Nat.le_refl _), hwf.eraseFrom]

/-- Byte zeroization touches only callee-owned allocations. Its memory
changes disappear at call-frame cleanup even though the stores are executed. -/
def zeroBytes (m : MemoryState) : List Pointer → MemoryState
  | [] => m
  | dst :: rest => zeroBytes (m.storeAt dst 0#8) rest

theorem zeroBytes_live (targets : List Pointer) (hr : SmallRange m p n) :
    SmallRange (zeroBytes m targets) p n := by
  induction targets generalizing m with
  | nil => exact hr
  | cons dst rest ih => exact ih (hr.storeAt _ _)

theorem zeroBytes_frame (targets : List Pointer) (m : MemoryState) (mark : Nat)
    (hinternal : ∀ p ∈ targets, mark ≤ p.id.id) :
    (zeroBytes m targets).eraseFrom mark = m.eraseFrom mark := by
  induction targets generalizing m with
  | nil => rfl
  | cons dst rest ih =>
    rw [zeroBytes, ih _ (fun p hp => hinternal p (by simp [hp]))]
    exact erase_internal_store _ _ _ _ _ rfl (hinternal dst (by simp))

end Agave.Ed25519.Verifier.Execution.SHA512Finalization

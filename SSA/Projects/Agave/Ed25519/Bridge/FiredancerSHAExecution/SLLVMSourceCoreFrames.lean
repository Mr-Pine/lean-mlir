import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreFeedforwardMemory

/-! Allocation and whole-live-memory frames for the scalar core's final stores
and removal of its private scratch allocation. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
open LeanMLIR SLLVM Firedancer
open Agave.Ed25519.SHA512.Spec
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] feedforwardMemory

theorem feedforwardMemory_dead (m : MemoryState) (chain : Pointer) (result : State)
    (b : BlockId) (hb : m.live? b = none) :
    (feedforwardMemory m chain result).live? b = none := by
  unfold feedforwardMemory
  iterate 8 apply live?_splice_eq_none
  exact hb

/-- Each concrete feedforward store preserves well-formedness. -/
theorem feedforwardState_wf (s : GlobalState) (chain : Pointer) (result : State)
    (hs : s.WF) : ({s with mem := feedforwardMemory s.mem chain result} : GlobalState).WF :=
  fun b hb => feedforwardMemory_dead s.mem chain result b (hs b hb)

theorem feedforwardState_alloc (s : GlobalState) (chain : Pointer) (result : State) :
    ({s with mem := feedforwardMemory s.mem chain result} : GlobalState).alloc = s.alloc := rfl

theorem feedforwardState_globals (s : GlobalState) (chain : Pointer) (result : State) :
    ({s with mem := feedforwardMemory s.mem chain result} : GlobalState).globals = s.globals := rfl

theorem SmallRange.feedforward {m : MemoryState} {p : Pointer} {n : Nat}
    (h : SmallRange m p n) (chain : Pointer) (result : State) :
    SmallRange (feedforwardMemory m chain result) p n := by
  unfold feedforwardMemory
  have h1 := h.splice chain result.a
  have h2 := h1.splice (chain.withOffset 8#64) result.b
  have h3 := h2.splice (chain.withOffset 16#64) result.c
  have h4 := h3.splice (chain.withOffset 24#64) result.d
  have h5 := h4.splice (chain.withOffset 32#64) result.e
  have h6 := h5.splice (chain.withOffset 40#64) result.f
  have h7 := h6.splice (chain.withOffset 48#64) result.g
  have h8 := h7.splice (chain.withOffset 56#64) result.h
  exact h8

/-- Splicing only consults the block being observed, whether it is the target
block or an untouched one. -/
theorem live_splice_congr {m m' : MemoryState} (p : Pointer) {w : Nat}
    (x : BitVec w) (b : BlockId) (h : m'.live? b = m.live? b) :
    (m'.splice p x).live? b = (m.splice p x).live? b := by
  by_cases he : p.id = b
  · subst b
    exact live?_splice_congr h
  · rw [live?_splice_ne he, live?_splice_ne he, h]

/-- A second store of equal width at the same pointer overwrites the first. -/
theorem live_splice_splice_self (m : MemoryState) (p : Pointer) {w : Nat}
    (x y : BitVec w) (b : BlockId) :
    ((m.splice p x).splice p y).live? b = (m.splice p y).live? b := by
  by_cases he : p.id = b
  · subst b
    cases hb : m.live? p.id with
    | none => rw [splicedDead (splicedDead hb), splicedDead hb]
    | some blk =>
      rw [splicedLive _ p _ (splicedLive m p blk hb x) y, splicedLive m p blk hb y]
      simp only [spliceBits_spliceBits_self]
  · rw [live?_splice_ne he, live?_splice_ne he, live?_splice_ne he]

/-- Popping kills every block at or above the restored allocation counter. -/
theorem popFrame_wf (before : GlobalState) (memory : MemoryState) :
    (before.popFrame memory).WF := by
  intro b hb
  exact live?_killFrom_of_le hb

/-- After removing scratch, the complete observable memory is the caller's
one-splice result. No hypothesis about the scratch block's contents is needed. -/
theorem scratch_popFrame_live (before middle : GlobalState) (chain : Pointer)
    {w : Nat} (out : BitVec w) (hwf : before.WF)
    (hframe : ∀ b : BlockId, b ≠ ⟨before.alloc.nextFreeBlock⟩ →
      middle.mem.live? b = (before.mem.splice chain out).live? b) :
    ∀ b, (before.popFrame middle.mem).mem.live? b =
      (before.mem.splice chain out).live? b := by
  intro b
  change (middle.mem.killFrom before.alloc.nextFreeBlock).live? b = _
  by_cases hb : b.id < before.alloc.nextFreeBlock
  · rw [live?_killFrom_of_lt hb]
    apply hframe
    intro he
    have hid := congrArg BlockId.id he
    simp only at hid
    omega
  · rw [live?_killFrom_of_le (by omega), live?_splice_eq_none (hwf b (by omega))]

/-- The same cleanup result packaged with restored caller metadata. -/
theorem scratch_popFrame_equiv (before middle : GlobalState) (chain : Pointer)
    {w : Nat} (out : BitVec w) (hwf : before.WF)
    (hframe : ∀ b : BlockId, b ≠ ⟨before.alloc.nextFreeBlock⟩ →
      middle.mem.live? b = (before.mem.splice chain out).live? b) :
    before.popFrame middle.mem ≈ ({before with mem := before.mem.splice chain out} : GlobalState) :=
  ⟨rfl, rfl, scratch_popFrame_live before middle chain out hwf hframe⟩

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core

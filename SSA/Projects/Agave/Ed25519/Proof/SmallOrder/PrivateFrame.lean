import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionContracts
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.CallMemory
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.ToBytesMemory

/-! Private-frame preservation for the actual allocations, field stores, and
canonical-byte stores used by point equality. Unlike a pre-cleanup read-only
claim, this invariant permits scratch memory to change and reclaims it at the
function's true entry allocation mark. -/
namespace Agave.Ed25519.SmallOrder.Execution
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
open LeanMLIR.RIR
open Verifier.Execution.Dalek (ReadOnlyFrame)

structure PrivateFrame (before current : GlobalState) : Prop where
  wellFormed : current.WF
  counter : before.alloc.nextFreeBlock ≤ current.alloc.nextFreeBlock
  memory : current.mem.eraseFrom before.alloc.nextFreeBlock = before.mem

namespace PrivateFrame

theorem refl (s : GlobalState) (hwf : s.WF) : PrivateFrame s s :=
  ⟨hwf, Nat.le_refl _, hwf.eraseFrom⟩

theorem alloca (h : PrivateFrame before current) (bytes : Nat) :
    PrivateFrame before (current.alloca bytes) := by
  refine ⟨h.wellFormed.alloca, ?_, ?_⟩
  · simpa only [GlobalState.alloca] using Nat.le_step h.counter
  · rw [GlobalState.eraseFrom_alloca_of_le h.counter, h.memory]

/-- A reclaimed lower call may advance the allocation counter. -/
theorem advance (h : PrivateFrame before current) (n : Nat) :
    PrivateFrame before {current with alloc := ⟨current.alloc.nextFreeBlock + n⟩} :=
  ⟨h.wellFormed.add_blocks, by have := h.counter; dsimp; omega,
    h.memory⟩

theorem storeAt (h : PrivateFrame before current) (dst : Pointer) (value : BitVec w)
    (hi : before.alloc.nextFreeBlock ≤ dst.id.id) :
    PrivateFrame before {current with mem := current.mem.storeAt dst value} := by
  refine ⟨h.wellFormed.storeAt, h.counter, ?_⟩
  rw [MemoryState.eraseFrom_storeAt, MemoryState.storeAt_eraseFrom_of_le hi, h.memory]

/-- All five actual field-kernel stores target the same private allocation. -/
theorem storeLimbs (h : PrivateFrame before current) (dst : Pointer)
    (value : Fin 5 → BitVec 64) (hi : before.alloc.nextFreeBlock ≤ dst.id.id) :
    PrivateFrame before
      {current with mem := SerialFieldMul.storeLimbs current.mem dst value} := by
  exact ((((h.storeAt dst (value 0) hi).storeAt (dst.add 8) (value 1) hi).storeAt
    (dst.add 16) (value 2) hi).storeAt (dst.add 24) (value 3) hi).storeAt
      (dst.add 32) (value 4) hi

/-- Each of the 32 emitted serialization stores stays within the private
byte-buffer allocation, irrespective of its stored value. -/
theorem storeBytes (h : PrivateFrame before current) (dst : Pointer)
    (value : Fin 32 → BitVec 8) (hi : before.alloc.nextFreeBlock ≤ dst.id.id) :
    PrivateFrame before {current with mem :=
      Encoding.Decompress.Execution.ToBytes.storeBytes current.mem dst value} := by
  have h0 := h.storeAt (dst.add 0) (value 0) hi
  have h1 := h0.storeAt (dst.add 1) (value 1) hi
  have h2 := h1.storeAt (dst.add 2) (value 2) hi
  have h3 := h2.storeAt (dst.add 3) (value 3) hi
  have h4 := h3.storeAt (dst.add 4) (value 4) hi
  have h5 := h4.storeAt (dst.add 5) (value 5) hi
  have h6 := h5.storeAt (dst.add 6) (value 6) hi
  have h7 := h6.storeAt (dst.add 7) (value 7) hi
  have h8 := h7.storeAt (dst.add 8) (value 8) hi
  have h9 := h8.storeAt (dst.add 9) (value 9) hi
  have h10 := h9.storeAt (dst.add 10) (value 10) hi
  have h11 := h10.storeAt (dst.add 11) (value 11) hi
  have h12 := h11.storeAt (dst.add 12) (value 12) hi
  have h13 := h12.storeAt (dst.add 13) (value 13) hi
  have h14 := h13.storeAt (dst.add 14) (value 14) hi
  have h15 := h14.storeAt (dst.add 15) (value 15) hi
  have h16 := h15.storeAt (dst.add 16) (value 16) hi
  have h17 := h16.storeAt (dst.add 17) (value 17) hi
  have h18 := h17.storeAt (dst.add 18) (value 18) hi
  have h19 := h18.storeAt (dst.add 19) (value 19) hi
  have h20 := h19.storeAt (dst.add 20) (value 20) hi
  have h21 := h20.storeAt (dst.add 21) (value 21) hi
  have h22 := h21.storeAt (dst.add 22) (value 22) hi
  have h23 := h22.storeAt (dst.add 23) (value 23) hi
  have h24 := h23.storeAt (dst.add 24) (value 24) hi
  have h25 := h24.storeAt (dst.add 25) (value 25) hi
  have h26 := h25.storeAt (dst.add 26) (value 26) hi
  have h27 := h26.storeAt (dst.add 27) (value 27) hi
  have h28 := h27.storeAt (dst.add 28) (value 28) hi
  have h29 := h28.storeAt (dst.add 29) (value 29) hi
  have h30 := h29.storeAt (dst.add 30) (value 30) hi
  have h31 := h30.storeAt (dst.add 31) (value 31) hi
  exact h31

/-- Reclaiming private storage establishes every memory observation, including
queries outside previously allocated ranges, required by the verifier frame. -/
theorem readOnly (h : PrivateFrame before current) (hwf : before.WF) :
    ReadOnlyFrame before
      {current with mem := current.mem.eraseFrom before.alloc.nextFreeBlock} := by
  constructor
  · intro id hid
    rw [h.memory] at hid
    exact lt_of_lt_of_le (hwf id hid) h.counter
  · intro q n hq
    simpa only [h.memory] using hq
  · intro q width
    rw [h.memory]

end PrivateFrame
end Agave.Ed25519.SmallOrder.Execution

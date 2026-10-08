import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendMessageRepresents
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMFinishAdapter
import SSA.Projects.Agave.Ed25519.Proof.SHA512.ByteOrder

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
namespace MessageExecution
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
attribute [local irreducible] append core Core.result sourceRead

def snapshotContext : Pointer := ⟨⟨0⟩, 0#64⟩
def snapshotData : Pointer := ⟨⟨1⟩, 0#64⟩

def snapshotInput (message : List (BitVec 8)) : LiveBlock :=
  ⟨message.length, BitVec.ofNat (8 * message.length)
    (Agave.Ed25519.Bridge.Challenge.decodeLE message)⟩

def snapshotState (block : LiveBlock) (message : List (BitVec 8)) : GlobalState :=
  ⟨⟨2⟩, ⟨((∅ : Std.HashMap BlockId Block).insert ⟨0⟩ (.live block)).insert
    ⟨1⟩ (.live (snapshotInput message))⟩, ∅⟩

theorem snapshot_context (block : LiveBlock) (message : List (BitVec 8)) :
    (snapshotState block message).mem.live? snapshotContext.id = some block := by
  simp only [snapshotState, snapshotContext, MemoryState.live?, MemoryState.getElem?_eq,
    Std.HashMap.getElem?_insert,
    show ((⟨1⟩ : BlockId) == ⟨0⟩) = false by decide, beq_self_eq_true, ↓reduceIte]
  rfl

theorem snapshot_data (block : LiveBlock) (message : List (BitVec 8)) :
    (snapshotState block message).mem.live? snapshotData.id = some (snapshotInput message) := by
  simp [snapshotState, snapshotData, MemoryState.live?, MemoryState.getElem?_eq]

theorem snapshot_context_range (block : LiveBlock) (message : List (BitVec 8))
    (hsmall : block.length < 2^63) (hlen : 224 ≤ block.length) :
    Core.SmallRange (snapshotState block message).mem snapshotContext 224 :=
  ⟨block, snapshot_context block message, hsmall, by simpa [snapshotContext]⟩

theorem snapshot_data_range (block : LiveBlock) (message : List (BitVec 8))
    (hsmall : message.length < 2^63) :
    Core.SmallRange (snapshotState block message).mem snapshotData message.length :=
  ⟨snapshotInput message, snapshot_data block message, hsmall, by simp [snapshotData, snapshotInput]⟩

theorem snapshot_bytes (block : LiveBlock) (message : List (BitVec 8))
    (hsmall : message.length < 2^63) :
    sourceReadBytes (snapshotState block message).mem snapshotData message.length = message := by
  rw [← FinishDigest.readBytes_sourceReadBytes _ _ _ (snapshot_data_range block message hsmall)]
  unfold Core.readBytes
  rw [FinishDigest.readBits_sourceRead]
  unfold sourceRead
  rw [snapshot_data]
  simpa [snapshotData, snapshotInput, Pointer.offsetInBits, Nat.mul_comm, Common.bytesOf,
    Agave.Ed25519.Bridge.Challenge.bytesOf] using
    Agave.Ed25519.SHA512.bytesOf_ofNat_decodeLE message

theorem live_splice_length (m : MemoryState) (q p : Pointer) (x : BitVec w) :
    ((m.splice q x).live? p.id).map LiveBlock.length =
      (m.live? p.id).map LiveBlock.length := by
  by_cases he : q.id = p.id
  · rw [← he, live_splice_storeBlock]
    simp only [storeBlock, Option.map_map]
    rfl
  · rw [live?_splice_ne he]

theorem resultState_context_length (s : GlobalState) (p data : Pointer) (n : BitVec 64) :
    ((resultState s p data n).mem.live? p.id).map LiveBlock.length =
      (s.mem.live? p.id).map LiveBlock.length := by
  unfold resultState
  split_ifs <;>
    simp (config := {failIfUnchanged := false}) only [coreState,
      appendMessageShortMemory, appendMessageFilledMemory,
      appendMessageTailMemory, appendMessageDirectTailMemory, live_splice_length]
  split <;> simp only [live_splice_length]

end MessageExecution
end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource

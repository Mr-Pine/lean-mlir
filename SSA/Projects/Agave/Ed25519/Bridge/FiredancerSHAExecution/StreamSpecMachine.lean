import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.Context
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.Arithmetic

/-! Relate the pure stream to the actual context observations and 64-bit
append size. Only an individual input chunk must fit a 64-bit size argument;
the accumulated transcript uses the implementation's full 128-bit counter. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge Agave.Ed25519.SHA512
open Agave.Ed25519.Verifier.Execution.Challenge

def observe (m : MemoryState) (context : Pointer) : Context :=
  ⟨Spec.pack (readState m context),
   readBytes m context (m.readAt (context.add 200#64) 64).toNat,
   m.readAt (context.add 216#64) 64 ++ m.readAt (context.add 208#64) 64⟩

theorem observe_represents (m : MemoryState) (context : Pointer)
    (completed buffer : Bytes) (h : ContextRepresents m context completed buffer) :
    Represents (observe m context) (completed ++ buffer) := by
  have hcount : (m.readAt (context.add 200#64) 64).toNat = buffer.length := by
    rw [h.pendingCount, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.pendingBound; omega)]
  have hbuffer : (observe m context).buffer = buffer := by
    change readBytes m context (m.readAt (context.add 200#64) 64).toNat = buffer
    rw [hcount, h.pendingBytes]
  refine ⟨completed, by rw [hbuffer], h.completedWhole, ?_, ?_, ?_⟩
  · rw [hbuffer]
    exact h.pendingBound
  · change Spec.pack (readState m context) = _
    rw [h.chaining, Spec.pack_unpack]
  · simpa only [observe, List.length_append] using h.bitCount

theorem finish_observe (m : MemoryState) (context : Pointer)
    (completed buffer : Bytes) (h : ContextRepresents m context completed buffer) :
    finish (observe m context) = digest Spec.compression (completed ++ buffer) :=
  finish_eq_digest _ _ (observe_represents m context completed buffer h)

/-- Every u64 input length has an exact 128-bit bit length before it is added
to the accumulated counter; extending before shifting avoids lost high bits. -/
theorem machine_chunk_bits (size : BitVec 64) :
    size.setWidth 128 <<< 3 = BitVec.ofNat 128 (8 * size.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have hs := size.isLt
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega : size.toNat < 2 ^ 128)]
  congr 1
  omega

/-- The source's two-word carry expression realizes the abstract update,
including when the low 64-bit word overflows. -/
theorem machine_counter_append (hi lo size : BitVec 64) (message chunk : Bytes)
    (hcount : hi ++ lo = BitVec.ofNat 128 (8 * message.length))
    (hsize : size.toNat = chunk.length) :
    appendHigh hi lo size ++ appendLow lo size =
      BitVec.ofNat 128 (8 * (message ++ chunk).length) := by
  rw [append_counter, hcount, machine_chunk_bits, hsize, ← BitVec.ofNat_add]
  congr 1
  simp [List.length_append, Nat.mul_add]

/-- The exact representability condition required by a single append call. -/
theorem size_represents_iff (n : Nat) :
    (∃ size : BitVec 64, size.toNat = n) ↔ n < 2 ^ 64 := by
  constructor
  · rintro ⟨size, rfl⟩
    exact size.isLt
  · intro hn
    exact ⟨BitVec.ofNat 64 n, by simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]⟩

theorem transcript_counter_no_overflow (r a : BitVec 256) (message : Bytes)
    (hsize : message.length < 2 ^ 64) :
    8 * (transcript r a message).length < 2 ^ 128 := by
  rw [transcript_length]
  omega

theorem transcript_counter_toNat (r a : BitVec 256) (message : Bytes)
    (hsize : message.length < 2 ^ 64) :
    ((append (append (append initial (bytesOf (n := 32) r))
      (bytesOf (n := 32) a)) message).bitCount).toNat = 8 * (64 + message.length) := by
  obtain ⟨_, _, _, _, _, hc⟩ := transcript_represents r a message
  rw [hc, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (transcript_counter_no_overflow r a message hsize), transcript_length]

/-- A chunk size near UINT64_MAX remains representable, although R || A || M
then exceeds UINT64_MAX bytes. No artificial 64-bit total-size premise is used. -/
theorem transcript_size_boundary :
    (2 ^ 64 - 1 : Nat) < 2 ^ 64 ∧
    ¬ (64 + (2 ^ 64 - 1 : Nat) < 2 ^ 64) ∧
    8 * (64 + (2 ^ 64 - 1 : Nat)) < 2 ^ 128 := by decide

end Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec

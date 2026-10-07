import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpecAppend

/-! Finalization branch equations and verifier transcript cutoffs. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec
open Agave.Ed25519.Bridge.Challenge Agave.Ed25519.SHA512
open Agave.Ed25519.Verifier.Execution.Challenge

theorem represents_buffer_length (s : Context) (message : Bytes)
    (h : Represents s message) : s.buffer.length = message.length % 128 := by
  obtain ⟨completed, hinput, hwhole, hbound, _, _⟩ := h
  have hlen := congrArg List.length hinput
  simp only [List.length_append] at hlen
  omega

/-- Original buffered bytes followed by the exact FIPS padding suffix. -/
theorem finishBlocks_flatten (s : Context) (message : Bytes)
    (h : Represents s message) :
    (finishBlocks s).flatten = s.buffer ++ suffix message.length := by
  rw [finishBlocks_eq s message h]
  have hp := (represents_buffer_length s message h).symm
  obtain ⟨_, _, _, hbound, _, _⟩ := h
  exact finalBlocks_flatten _ _ hbound hp

theorem finish_short (s : Context) (message : Bytes)
    (h : Represents s message) (hshort : s.buffer.length < 112) :
    finish s = serialize (Spec.compressBlockBytes s.chain
      (onlyPaddingBlock s.buffer message.length)) := by
  unfold finish
  rw [finishBlocks_eq s message h]
  simp only [finalBlocks, ite_eq_left hshort, List.foldl_cons, List.foldl_nil]
  rw [Spec.run_one_block _ _ (onlyPaddingBlock_length _ hshort)]

theorem finish_long (s : Context) (message : Bytes)
    (h : Represents s message) (hlong : 112 ≤ s.buffer.length) :
    finish s = serialize (Spec.compressBlockBytes
      (Spec.compressBlockBytes s.chain (firstPaddingBlock s.buffer))
      (lastPaddingBlock message.length)) := by
  have hbound : s.buffer.length < 128 := by
    obtain ⟨_, _, _, hb, _, _⟩ := h
    exact hb
  unfold finish
  rw [finishBlocks_eq s message h]
  simp only [finalBlocks, ite_eq_right (by omega : ¬s.buffer.length < 112),
    List.foldl_cons, List.foldl_nil]
  rw [Spec.run_one_block _ _ (firstPaddingBlock_length _ hbound),
    Spec.run_one_block _ _ (lastPaddingBlock_length _)]

/-- Both 32-byte appends are buffered; neither performs compression. -/
theorem transcript_prefix (r a : BitVec 256) :
    append (append initial (bytesOf (n := 32) r)) (bytesOf (n := 32) a) =
      ⟨initialWords, bytesOf (n := 32) r ++ bytesOf (n := 32) a, 512⟩ := by
  rw [append_short initial _ (by simp [initial])]
  rw [append_short _ _ (by simp [initial])]
  simp [initial]

theorem transcript_pending_length (r a : BitVec 256) (message : Bytes) :
    (append (append (append initial (bytesOf (n := 32) r))
      (bytesOf (n := 32) a)) message).buffer.length = (64 + message.length) % 128 := by
  simpa using represents_buffer_length _ _ (transcript_represents r a message)

/-- R and A occupy the first 64 transcript bytes. Consequently the long
padding path is selected exactly for message residues 48 through 63. -/
theorem transcript_long_padding_iff (r a : BitVec 256) (message : Bytes) :
    112 ≤ (append (append (append initial (bytesOf (n := 32) r))
      (bytesOf (n := 32) a)) message).buffer.length ↔
      48 ≤ message.length % 128 ∧ message.length % 128 < 64 := by
  rw [transcript_pending_length]
  have hmod : (64 + message.length) % 128 = (64 + message.length % 128) % 128 := by
    omega
  rw [hmod]
  omega

end Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec

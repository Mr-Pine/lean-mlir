import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec

/-! Reblocking equations for the C append branches: fill the old buffer,
compress the completed first block, process direct input blocks, retain tail. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec
open Agave.Ed25519.Bridge.Challenge Agave.Ed25519.SHA512

theorem complete_append_aligned (xs ys : Bytes) (hx : xs.length % 128 = 0) :
    complete (xs ++ ys) = xs ++ complete ys := by
  have hcut : 128 * ((xs.length + ys.length) / 128) =
      xs.length + 128 * (ys.length / 128) := by omega
  simp only [complete, List.length_append, hcut, List.take_append]
  rw [List.take_of_length_le (by omega : xs.length ≤ xs.length + 128 * (ys.length / 128))]
  simp

theorem pending_append_aligned (xs ys : Bytes) (hx : xs.length % 128 = 0) :
    pending (xs ++ ys) = pending ys := by
  have hcut : 128 * ((xs.length + ys.length) / 128) =
      xs.length + 128 * (ys.length / 128) := by omega
  simp only [pending, List.length_append, hcut, List.drop_append]
  rw [List.drop_of_length_le (by omega : xs.length ≤ xs.length + 128 * (ys.length / 128))]
  simp

theorem append_short (s : Context) (chunk : Bytes)
    (h : s.buffer.length + chunk.length < 128) :
    append s chunk =
      ⟨s.chain, s.buffer ++ chunk, s.bitCount + BitVec.ofNat 128 (8 * chunk.length)⟩ := by
  have hq : (s.buffer.length + chunk.length) / 128 = 0 := by omega
  simp [append, complete, pending, hq]

def filledBlock (buffer chunk : Bytes) : Bytes :=
  buffer ++ chunk.take (128 - buffer.length)

theorem filledBlock_length (buffer chunk : Bytes)
    (hb : buffer.length < 128) (hc : 128 - buffer.length ≤ chunk.length) :
    (filledBlock buffer chunk).length = 128 := by
  simp only [filledBlock, List.length_append, List.length_take, Nat.min_eq_left hc]
  omega

theorem filledBlock_partition (buffer chunk : Bytes) :
    filledBlock buffer chunk ++ chunk.drop (128 - buffer.length) = buffer ++ chunk := by
  simp [filledBlock, List.append_assoc]

/-- Exactly the first-block/direct-block/tail decomposition of a buffer-filling
append. The extra counter update depends on the entire chunk, once only. -/
theorem append_filled (s : Context) (chunk : Bytes)
    (hb : s.buffer.length < 128) (hc : 128 - s.buffer.length ≤ chunk.length) :
    append s chunk =
      ⟨Spec.run (Spec.compressBlockBytes s.chain (filledBlock s.buffer chunk))
         (complete (chunk.drop (128 - s.buffer.length))),
       pending (chunk.drop (128 - s.buffer.length)),
       s.bitCount + BitVec.ofNat 128 (8 * chunk.length)⟩ := by
  have hf := filledBlock_length s.buffer chunk hb hc
  have hw : (filledBlock s.buffer chunk).length % 128 = 0 := by rw [hf]
  unfold append
  rw [← filledBlock_partition s.buffer chunk, complete_append_aligned _ _ hw,
    pending_append_aligned _ _ hw, Spec.run_append _ _ _ hw,
    Spec.run_one_block _ _ hf]

theorem append_empty_buffer (s : Context) (chunk : Bytes) (h : s.buffer = []) :
    append s chunk =
      ⟨Spec.run s.chain (complete chunk), pending chunk,
       s.bitCount + BitVec.ofNat 128 (8 * chunk.length)⟩ := by
  simp [append, h]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec

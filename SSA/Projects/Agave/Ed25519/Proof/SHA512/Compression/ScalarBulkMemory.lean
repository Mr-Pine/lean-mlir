import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullFuel
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ContextContract

/-! Live suffixes and exact pointer arithmetic for the scalar block loop. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open Spec

theorem subrange (h : SmallRange mem data bytes) (hk : offset + count ≤ bytes) :
    SmallRange mem (data.add (BitVec.ofNat 64 offset)) count := by
  have hn : offset < 2 ^ 64 := by have := h.offset_lt; norm_num at *; omega
  have hov := h.no_wrap (k := offset) (by omega)
  obtain ⟨b, hb, hsmall, hsize⟩ := h
  refine ⟨b, ?_, hsmall, ?_⟩
  · simpa only [Pointer.add_id] using hb
  · simpa only [Pointer.add, BitVec.toNat_add_of_not_uaddOverflow hov,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] using (by omega : data.offset.toNat + offset + count ≤ b.length)

theorem live_prefix (h : SmallRange mem data bytes) (hn : count ≤ bytes) :
    SmallRange mem data count := by
  simpa only [Pointer.add_zero] using subrange h (offset := 0) (by simpa using hn)

theorem next_end (data : Pointer) (n : Nat) :
    (data.add 128#64).add (BitVec.ofNat 64 (128 * n)) =
      data.add (BitVec.ofNat 64 (128 * (n + 1))) := by
  rw [Pointer.add_add]
  congr 1
  rw [← BitVec.ofNat_add]
  congr 1
  omega

theorem next_ne_end (data : Pointer) (n : Nat)
    (hd : SmallRange mem data (128 * (n + 2))) :
    (data.add 128#64).offset ≠ (data.add (BitVec.ofNat 64 (128 * (n + 2)))).offset := by
  have hn : 128 * (n + 2) < 2 ^ 64 := by have := hd.offset_lt; norm_num at *; omega
  have h0 := hd.no_wrap (k := 128) (by omega)
  have h1 := hd.no_wrap (k := 128 * (n + 2)) (by omega)
  intro heq
  have he := congrArg BitVec.toNat heq
  simp only [Pointer.add, BitVec.toNat_add_of_not_uaddOverflow h0,
    BitVec.toNat_add_of_not_uaddOverflow h1, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn] at he
  norm_num at he

theorem run_readBytes_succ (initial : Spec.State) (mem : MemoryState) (data : Pointer) (n : Nat) :
    Spec.run (pack initial) (readBytes mem data (128 * (n + 1))) =
      Spec.run (pack (compressBlock initial (readBytes mem data 128)))
        (readBytes mem (data.add 128#64) (128 * n)) := by
  rw [show 128 * (n + 1) = 128 + 128 * n by omega, readBytes_append,
    Spec.run_append _ _ _ (by simp)]
  rw [Spec.run_one_block (pack initial) (readBytes mem data 128) (by simp)]
  simp only [compressBlockBytes, unpack_pack]

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk

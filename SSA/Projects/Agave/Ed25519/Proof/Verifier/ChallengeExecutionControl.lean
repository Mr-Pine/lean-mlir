import SSA.Projects.Agave.Ed25519.Bridge.ChallengeBytes
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-!
Arithmetic and byte-order facts needed by the extracted `challenge_scalar`.
These lemmas do not assert execution refinement. The compiled body buffers
R || A, processes complete 128-byte blocks, and hands a 208-byte incremental
SHA-512 context to `scalar_from_sha512`; padding belongs to that callee.
-/

namespace Agave.Ed25519.Verifier.Execution.Challenge

open LeanMLIR.RIR
open Agave.Ed25519.Bridge.Challenge

/-- Bytes actually supplied to the incremental SHA-512 implementation. -/
def transcript (r a : BitVec 256) (message : Bytes) : Bytes :=
  bytesOf (n := 32) r ++ bytesOf (n := 32) a ++ message

@[simp] theorem transcript_length (r a : BitVec 256) (message : Bytes) :
    (transcript r a message).length = 64 + message.length := by
  simp [transcript]
  omega

/-- The first full compression block after the two 32-byte inputs. -/
def firstBlock (r a : BitVec 256) (message : Bytes) : Bytes :=
  bytesOf (n := 32) r ++ bytesOf (n := 32) a ++ message.take 64

theorem firstBlock_length (r a : BitVec 256) (message : Bytes)
    (h : 64 ≤ message.length) : (firstBlock r a message).length = 128 := by
  simp [firstBlock, Nat.min_eq_left h]

/-- The first compression and the direct-message compression consume the
original bytes in order, without point decoding or re-encoding. -/
theorem transcript_split (r a : BitVec 256) (message : Bytes) :
    transcript r a message = firstBlock r a message ++ message.drop 64 := by
  simp [transcript, firstBlock, List.append_assoc]

theorem direct_blocks_and_tail (message : Bytes) :
    (message.drop 64).take (128 * ((message.length - 64) / 128)) ++
      (message.drop 64).drop (128 * ((message.length - 64) / 128)) =
      message.drop 64 := List.take_append_drop _ _

theorem tail_length (message : Bytes) :
    ((message.drop 64).drop (128 * ((message.length - 64) / 128))).length =
      (message.length - 64) % 128 := by
  simp only [List.length_drop]
  omega

theorem long_transcript_blocks (r a : BitVec 256) (message : Bytes) :
    transcript r a message =
      firstBlock r a message ++
        (message.drop 64).take (128 * ((message.length - 64) / 128)) ++
        (message.drop 64).drop (128 * ((message.length - 64) / 128)) := by
  rw [List.append_assoc, direct_blocks_and_tail, transcript_split]

/-- RIR register 37 is the count of complete SHA blocks in the remaining slice. -/
theorem full_block_count (x : BitVec 64) : (x >>> 7).toNat = x.toNat / 128 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- RIR register 39 is the remaining buffer length. -/
theorem remaining_byte_count (x : BitVec 64) :
    (x &&& 127).toNat = x.toNat % 128 := by
  simpa using Nat.and_two_pow_sub_one_eq_mod x.toNat 7

private theorem mask_offset_nat (n : Nat) (h : n < 2 ^ 63) :
    n &&& 9223372036854775680 = 128 * (n / 128) := by
  have hdiv : n / 128 < 2 ^ 56 := by omega
  have hquot : (n &&& 9223372036854775680) / 128 = n / 128 := by
    change (n &&& 9223372036854775680) / 2 ^ 7 = n / 128
    rw [Nat.and_div_two_pow]
    change n / 128 &&& (2 ^ 56 - 1) = n / 128
    exact Nat.and_two_pow_sub_one_of_lt_two_pow hdiv
  have hmod : (n &&& 9223372036854775680) % 128 = 0 := by
    change (n &&& 9223372036854775680) % 2 ^ 7 = 0
    rw [Nat.and_mod_two_pow]
    simp
  omega

/-- RIR's signed-slice mask clears the bottom seven bits and the sign bit.
The latter is already zero for every legal Rust slice. -/
theorem full_block_offset (x : BitVec 64) (h : x.toNat < 2 ^ 63) :
    (x &&& 9223372036854775680).toNat = 128 * (x.toNat / 128) := by
  simpa using mask_offset_nat x.toNat h

theorem offset_plus_tail (x : BitVec 64) (h : x.toNat < 2 ^ 63) :
    (x &&& 9223372036854775680).toNat + (x &&& 127).toNat = x.toNat := by
  rw [full_block_offset x h, remaining_byte_count]
  omega

/-- The 128-bit block counter and the one-byte residual buffer count describe
the exact transcript length, including the initial 64 bytes. -/
theorem total_length_accounting (n : Nat) (h : 64 ≤ n) :
    128 * (1 + (n - 64) / 128) + (n - 64) % 128 = 64 + n := by
  omega

theorem block_count_fits (n : Nat) (h : n < 2 ^ 63) :
    1 + (n - 64) / 128 < 2 ^ 128 := by
  omega

theorem buffer_count_fits (n : Nat) : n % 128 < 128 := Nat.mod_lt _ (by decide)

/-- In the short path, `%34 = 64 + trunc(%arg4)` is representable even with
the emitted unsigned-no-overflow flag. -/
theorem short_buffer_count (x : BitVec 64) (h : x.toNat < 64) :
    ((64 : BitVec 8) + x.setWidth 8).toNat = 64 + x.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_setWidth]
  norm_num
  omega

theorem short_buffer_no_overflow (x : BitVec 64) (h : x.toNat < 64) :
    ¬(64 : BitVec 8).uaddOverflow (x.setWidth 8) := by
  simp only [BitVec.uaddOverflow, BitVec.toNat_setWidth]
  norm_num
  omega

/-- Both emitted truncation flags are justified by the seven-bit residual.
In particular, signed truncation cannot turn bytes 128–255 into negatives. -/
theorem trunc8_flags (x : BitVec 64) (h : x.toNat < 128) :
    Operation.trunc { nsw := true, nuw := true } (.value x) =
      (.value (x.setWidth 8) : PoisonOr (BitVec 8)) := by
  have hz : (x.setWidth 8).setWidth 64 = x := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    norm_num
    omega
  have hm : (x.setWidth 8).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]
    simp only [BitVec.toNat_setWidth]
    norm_num
    omega
  have hs : (x.setWidth 8).signExtend 64 = x := by
    rw [BitVec.signExtend_eq_setWidth_of_msb_false hm, hz]
  simp [Operation.trunc, hz, hs]

theorem short_buffer_add_flags (x : BitVec 64) (h : x.toNat < 64) :
    Operation.add { nuw := true } (.value (64 : BitVec 8)) (.value (x.setWidth 8)) =
      .value ((64 : BitVec 8) + x.setWidth 8) := by
  have hu : ¬(64#8).uaddOverflow (x.setWidth 8) := short_buffer_no_overflow x h
  simp [Operation.add, hu]

/-- The long path removes the 64 message bytes that fill the initial block.
The signed and unsigned subtraction flags are both safe on legal slices. -/
theorem message_sub_flags (x : BitVec 64) (hlo : 64 ≤ x.toNat)
    (hhi : x.toNat < 2 ^ 63) :
    Operation.sub { nsw := true, nuw := true } (.value x) (.value 64) =
      .value (x - 64) := by
  have hx : x.toInt = (x.toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by norm_num at *; omega)
  have hu : ¬x.usubOverflow 64#64 := by
    simp [BitVec.usubOverflow]
    omega
  have hs : ¬x.ssubOverflow 64#64 := by
    simp [BitVec.ssubOverflow, hx]
    norm_num at *
    omega
  simp [Operation.sub, hu, hs]

theorem block_shift_defined (x : BitVec 64) :
    Operation.lshr false (.value x) (.value 7) = .value (x >>> 7) := by
  simp [Operation.lshr]

theorem block_count_zext_defined (x : BitVec 64) (h : x.toNat < 2 ^ 63) :
    Operation.zext true (.value (x >>> 7)) =
      (.value ((x >>> 7).setWidth 128) : PoisonOr (BitVec 128)) := by
  have hm : (x >>> 7).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, full_block_count]
    norm_num at *
    omega
  simp [Operation.zext, hm]

/-- The direct-message offset is inside the original message allocation;
the tail memcpy reads exactly the bytes after that offset. -/
theorem long_pointer_bounds (n : Nat) (h : 64 ≤ n) :
    64 + 128 * ((n - 64) / 128) ≤ n ∧
    64 + 128 * ((n - 64) / 128) + (n - 64) % 128 = n := by
  omega

end Agave.Ed25519.Verifier.Execution.Challenge

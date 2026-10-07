import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.EntryTail

/-! Byte-order identities connecting the exact RIR `bswap` expression and
SHA-512's digest/length-field specifications. No hash or execution assumptions.
The finite bit proofs use only kernel-checked simplification. -/
namespace Agave.Ed25519.SHA512

open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.SHA512Finalization

set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

/-- Reading byte `i` of a swapped u64 reads byte `7-i` of the original. -/
theorem swapBytes64_byte (value : BitVec 64) (i : Nat) (hi : i < 8) :
    (swapBytes value).extractLsb' (8 * i) 8 = value.extractLsb' (8 * (7 - i)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  interval_cases i <;> interval_cases j <;>
    simp [swapBytes, List.range_succ, List.foldl_append, BitVec.getLsbD_or,
      BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_extractLsb']

/-- Reading byte `i` of a swapped u128 reads byte `15-i` of the original. -/
theorem swapBytes128_byte (value : BitVec 128) (i : Nat) (hi : i < 16) :
    (swapBytes value).extractLsb' (8 * i) 8 = value.extractLsb' (8 * (15 - i)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  interval_cases i <;> interval_cases j <;>
    simp [swapBytes, List.range_succ, List.foldl_append, BitVec.getLsbD_or,
      BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_extractLsb']

/-- The bytes of the actual bswap128 length store are exactly the abstract
SHA-512 big-endian bit-length field, including modulo-2^128 truncation. -/
theorem swapBytes128_lengthField (total : Nat) :
    bytesOf (n := 16) (swapBytes (BitVec.ofNat 128 (8 * total))) = lengthField total := by
  unfold bytesOf lengthField
  congr 1
  funext i
  simpa [Nat.mul_comm] using swapBytes128_byte (BitVec.ofNat 128 (8 * total)) i.val i.isLt

/-- The converse byte decoding/encoding identity, with byte range built into
`BitVec 8`; it does not need a separate boundedness premise. -/
theorem encodeLE_decodeLE (bytes : Bytes) : encodeLE bytes.length (decodeLE bytes) = bytes := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    have hbyte : byte.toNat < 256 := byte.isLt
    have hlo : BitVec.ofNat 8 (byte.toNat + 256 * decodeLE rest) = byte := by
      apply BitVec.eq_of_toNat_eq
      change (byte.toNat + 256 * decodeLE rest) % 256 = byte.toNat
      omega
    have hhi : (byte.toNat + 256 * decodeLE rest) / 256 = decodeLE rest := by omega
    simp only [List.length_cons, encodeLE, decodeLE]
    rw [hlo, hhi, ih]

/-- Assemble the bytes as a little-endian bitvector and read them back. -/
theorem bytesOf_ofNat_decodeLE (bytes : Bytes) :
    bytesOf (BitVec.ofNat (bytes.length * 8) (decodeLE bytes)) = bytes := by
  rw [bytesOf_eq_encodeLE, BitVec.toNat_ofNat, ← radix_pow,
    Nat.mod_eq_of_lt (decodeLE_lt bytes), encodeLE_decodeLE]

/-- Fixed-width form of byte assembly, avoiding dependent casts when the
byte-list length is known propositionally rather than definitionally. -/
theorem bytesOf_ofNat_decodeLE_of_length (bytes : Bytes) (n : Nat)
    (hlen : bytes.length = n) :
    bytesOf (n := n) (BitVec.ofNat (n * 8) (decodeLE bytes)) = bytes := by
  subst n
  exact bytesOf_ofNat_decodeLE bytes

/-- The natural-number fold used by `serialize` is byte decoding. Proving this
for arbitrary counts avoids normalizing the 64-byte sum into a huge numeral. -/
theorem weighted_fold_decodeLE (byte : Nat → BitVec 8) (n : Nat) :
    (List.range n).foldl (fun acc i => acc + (byte i).toNat * 2 ^ (8 * i)) 0 =
      decodeLE (List.ofFn fun i : Fin n => byte i.val) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, ih]
    rw [List.ofFn_succ_last, decodeLE_append]
    simp only [Fin.val_castSucc, Fin.val_last, List.length_ofFn, decodeLE,
      Nat.mul_zero, Nat.add_zero]
    rw [radix_pow]
    simp only [Nat.mul_comm]

/-- Exact per-byte meaning of the digest serializer consumed by the scalar
reducer. The output is eight big-endian u64 words in their original order. -/
theorem bytesOf_serialize (state : BitVec 512) :
    bytesOf (n := 64) (serialize state) =
      List.ofFn (fun i : Fin 64 =>
        state.extractLsb' (64 * (i.val / 8) + 8 * (7 - i.val % 8)) 8) := by
  let byte := fun i : Nat => state.extractLsb' (64 * (i / 8) + 8 * (7 - i % 8)) 8
  have hfold := weighted_fold_decodeLE byte 64
  change bytesOf (n := 64) (BitVec.ofNat 512
    ((List.range 64).foldl (fun acc i => acc + (byte i).toNat * 2 ^ (8 * i)) 0)) = _
  rw [hfold]
  exact bytesOf_ofNat_decodeLE_of_length (List.ofFn fun i : Fin 64 => byte i.val)
    64 List.length_ofFn

/-- Readback at byte granularity, useful when stitching the actual eight
memory stores to the full 512-bit digest. -/
theorem serialize_byte (state : BitVec 512) (i : Fin 64) :
    (serialize state).extractLsb' (8 * i.val) 8 =
      state.extractLsb' (64 * (i.val / 8) + 8 * (7 - i.val % 8)) 8 := by
  have h := congrArg (fun bytes : Bytes => bytes[i.val]?) (bytesOf_serialize state)
  simpa only [bytesOf, List.getElem?_ofFn, dif_pos i.isLt, Option.some.injEq,
    Nat.mul_comm] using h

/-- Byte equality determines the complete byte-aligned word. -/
theorem bytesOf_injective {n : Nat} {left right : BitVec (n * 8)}
    (h : bytesOf left = bytesOf right) : left = right := by
  apply BitVec.eq_of_toNat_eq
  have hd := congrArg decodeLE h
  simpa only [decodeLE_bytesOf] using hd

/-- Nested in-range extraction, convenient for digest word/byte readback. -/
theorem extract_nested (value : BitVec width) (start outer offset count : Nat)
    (h : offset + count ≤ outer) :
    (value.extractLsb' start outer).extractLsb' offset count =
      value.extractLsb' (start + offset) count := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have ho : offset + j < outer := by omega
  simp [BitVec.getLsbD_extractLsb', hj, ho, Nat.add_assoc]

/-- The full digest's ith u64 is exactly the bswap value stored by the
extracted wrapper; this lets memory stitching proceed word by word. -/
theorem serialize_word (state : BitVec 512) (i : Nat) (hi : i < 8) :
    (serialize state).extractLsb' (64 * i) 64 =
      swapBytes (state.extractLsb' (64 * i) 64) := by
  apply bytesOf_injective (n := 8)
  unfold bytesOf
  congr 1
  funext j
  have hj : j.val < 8 := j.isLt
  simp only [Nat.mul_comm j.val 8]
  rw [extract_nested (serialize state) (64 * i) 64 (8 * j.val) 8 (by omega),
    swapBytes64_byte _ j.val hj,
    extract_nested state (64 * i) 64 (8 * (7 - j.val)) 8 (by omega)]
  have hindex : 64 * i + 8 * j.val = 8 * (8 * i + j.val) := by omega
  rw [hindex, serialize_byte state ⟨8 * i + j.val, by omega⟩]
  have hdiv : (8 * i + j.val) / 8 = i := by omega
  have hmod : (8 * i + j.val) % 8 = j.val := by omega
  simp only [hdiv, hmod]

end Agave.Ed25519.SHA512

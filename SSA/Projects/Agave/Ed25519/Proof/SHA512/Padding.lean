import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionState

/-!
SHA-512 padding, byte serialization, and the finalization control split shared
by both clients. Compression is an explicit parameter, not a custom axiom.
The digest is DEFINED from compression and padding: there is no independent
whole-hash equality premise. This semantic layer is not a proof of the
70-allocation, zeroizing `scalar_from_sha512` machine-code wrapper.
-/
namespace Agave.Ed25519.SHA512

open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Bridge.Challenge

/-- Address-order big-endian encoding of SHA-512's 128-bit bit-length field.
Truncation modulo 2^128 is explicit, as in the extracted LLVM arithmetic. -/
def lengthField (bytes : Nat) : Bytes :=
  List.ofFn fun i : Fin 16 =>
    (BitVec.ofNat 128 (8 * bytes)).extractLsb' (8 * (15 - i.val)) 8

@[simp] theorem lengthField_length (bytes : Nat) :
    (lengthField bytes).length = 16 := by simp [lengthField]

/-- Number of zeros after the mandatory 0x80 byte. -/
def zeroCount (n : Nat) : Nat := (239 - n % 128) % 128

/-- FIPS SHA-512 padding suffix, including the length in bits. -/
def suffix (n : Nat) : Bytes :=
  [128] ++ List.replicate (zeroCount n) 0 ++ lengthField n

/-- The one/two-block branch emitted by the pinned Rust compiler. -/
def needsTwoBlocks (pending : BitVec 8) : Bool :=
  (pending.setWidth 64 ^^^ (112 : BitVec 64)).ult 16

/-- The exact emitted XOR/compare implements the SHA-512 cutoff at 112.
Enumeration is over the 128 legal buffer lengths and checked by the kernel. -/
theorem needsTwoBlocks_iff (pending : BitVec 8) (h : pending.toNat < 128) :
    needsTwoBlocks pending = true ↔ 112 ≤ pending.toNat := by
  have hp : pending = BitVec.ofNat 8 pending.toNat := by simp
  rw [hp]
  generalize pending.toNat = n at *
  interval_cases n <;> decide

/-- The emitted disjoint OR is exactly the full transcript bit count, for
all lengths that fit SHA-512's 128-bit length field. -/
theorem bitLength_arithmetic (blocks : BitVec 128) (pending : BitVec 8)
    (hb : blocks.toNat < 2 ^ 118) (hp : pending.toNat < 128) :
    ((blocks <<< 10) ||| (pending.setWidth 128 <<< 3)) =
      BitVec.ofNat 128 (8 * (128 * blocks.toNat + pending.toNat)) := by
  apply BitVec.eq_of_toNat_eq
  have hs : pending.toNat < 2 ^ 128 := by omega
  have hlo : pending.toNat <<< 3 < 2 ^ 10 := by
    simp only [Nat.shiftLeft_eq]
    omega
  have hb' : blocks.toNat <<< 10 < 2 ^ 128 := by
    simp only [Nat.shiftLeft_eq]
    omega
  have hp' : pending.toNat <<< 3 < 2 ^ 128 := by omega
  have ht : 8 * (128 * blocks.toNat + pending.toNat) < 2 ^ 128 := by omega
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hb', Nat.mod_eq_of_lt hp',
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht]
  rw [← Nat.shiftLeft_add_eq_or_of_lt hlo]
  simp only [Nat.shiftLeft_eq]
  omega

/-- The first full block on the long-padding path. -/
def firstPaddingBlock (pending : Bytes) : Bytes :=
  pending ++ [128] ++ List.replicate (127 - pending.length) 0

/-- The second full block on the long-padding path. -/
def lastPaddingBlock (total : Nat) : Bytes :=
  List.replicate 112 0 ++ lengthField total

/-- A single full block on the short-padding path. -/
def onlyPaddingBlock (pending : Bytes) (total : Nat) : Bytes :=
  pending ++ [128] ++ List.replicate (111 - pending.length) 0 ++ lengthField total

/-- The exact order and number of compression inputs selected by finalization. -/
def finalBlocks (pending : Bytes) (total : Nat) : List Bytes :=
  if pending.length < 112 then [onlyPaddingBlock pending total]
  else [firstPaddingBlock pending, lastPaddingBlock total]

@[simp] theorem firstPaddingBlock_length (pending : Bytes) (h : pending.length < 128) :
    (firstPaddingBlock pending).length = 128 := by
  simp [firstPaddingBlock]
  omega

@[simp] theorem lastPaddingBlock_length (total : Nat) :
    (lastPaddingBlock total).length = 128 := by simp [lastPaddingBlock]

@[simp] theorem onlyPaddingBlock_length (pending : Bytes) (h : pending.length < 112) :
    (onlyPaddingBlock pending total).length = 128 := by
  simp [onlyPaddingBlock]
  omega

theorem finalBlocks_whole (pending : Bytes) (total : Nat) (h : pending.length < 128) :
    ∀ block ∈ finalBlocks pending total, block.length = 128 := by
  unfold finalBlocks
  split_ifs with hs
  · simpa using onlyPaddingBlock_length pending hs
  · simp [firstPaddingBlock_length pending h]

/-- No already-compressed byte is rehashed, and no pending byte is omitted.
The concatenated compression inputs are the pending bytes followed by precisely
the canonical SHA-512 suffix for the entire original transcript. -/
theorem finalBlocks_flatten (pending : Bytes) (total : Nat)
    (h : pending.length < 128) (htotal : total % 128 = pending.length) :
    (finalBlocks pending total).flatten = pending ++ suffix total := by
  have hz : zeroCount total =
      if pending.length < 112 then 111 - pending.length else 239 - pending.length := by
    unfold zeroCount
    rw [htotal]
    split_ifs <;> omega
  unfold finalBlocks
  split_ifs with hs
  · simp [onlyPaddingBlock, suffix, hz, hs, List.append_assoc]
  · have hsum : 239 - pending.length = (127 - pending.length) + 112 := by omega
    simp [firstPaddingBlock, lastPaddingBlock, suffix, hz, hs, hsum,
      List.replicate_add, List.append_assoc]

/-- Complete-block compression specification. The only algebraic law needed
by the wrapper proof is composition on block-aligned input. A future concrete
80-round implementation can inhabit this interface without changing padding. -/
structure Compression where
  run : BitVec 512 → Bytes → BitVec 512
  empty : ∀ state, run state [] = state
  append : ∀ state xs ys, xs.length % 128 = 0 → ys.length % 128 = 0 →
    run state (xs ++ ys) = run (run state xs) ys

/-- SHA outputs each native chaining word in big-endian byte order, while the
Ed25519 scalar reducer interprets the resulting 64 bytes little-endian. -/
def serialize (state : BitVec 512) : BitVec 512 :=
  BitVec.ofNat 512 ((List.range 64).foldl (fun acc i =>
    acc + ((state.extractLsb' (64 * (i / 8) + 8 * (7 - i % 8)) 8).toNat * 2 ^ (8 * i))) 0)

/-- Shared digest with padding and serialization fixed by definition. Only
complete-block compression remains abstract. -/
def digest (compress : Compression) (message : Bytes) : BitVec 512 :=
  serialize (compress.run initialWords (message ++ suffix message.length))

/-- Instantiate the existing challenge ABI with a digest constructed from
compression, preventing an unrelated arbitrary whole-hash function. -/
def model (compress : Compression) : Sha512Model where
  compress := compress.run
  digest := digest compress
  empty := compress.empty
  append := compress.append

/-- Semantic execution of the extracted one/two-compression finalization. -/
def finalize (compress : Compression) (state : BitVec 512)
    (pending : Bytes) (total : Nat) : BitVec 512 :=
  serialize ((finalBlocks pending total).foldl compress.run state)

theorem finalBlocks_fold (compress : Compression) (state : BitVec 512)
    (pending : Bytes) (total : Nat) (h : pending.length < 128) :
    (finalBlocks pending total).foldl compress.run state =
      compress.run state (finalBlocks pending total).flatten := by
  unfold finalBlocks
  split_ifs with hs
  · simp
  · simp only [List.foldl_cons, List.foldl_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil]
    symm
    exact compress.append state _ _ (by simp [firstPaddingBlock_length pending h])
      (by simp)

theorem finalBlocks_flatten_whole (pending : Bytes) (total : Nat)
    (h : pending.length < 128) : (finalBlocks pending total).flatten.length % 128 = 0 := by
  unfold finalBlocks
  split_ifs with hs
  · simp [onlyPaddingBlock_length pending hs]
  · simp [firstPaddingBlock_length pending h]

/-- Compression-only semantic refinement of finalization. There is no digest
correctness assumption: the shared digest is derived from the exact bytes. -/
theorem finalize_eq_digest (compress : Compression) (completed pending : Bytes)
    (hwhole : completed.length % 128 = 0) (hbound : pending.length < 128) :
    finalize compress (compress.run initialWords completed) pending
      (completed.length + pending.length) = digest compress (completed ++ pending) := by
  have ht : (completed.length + pending.length) % 128 = pending.length := by omega
  have hb := finalBlocks_flatten pending _ hbound ht
  have hw := finalBlocks_flatten_whole pending (completed.length + pending.length) hbound
  rw [hb] at hw
  unfold finalize digest
  rw [finalBlocks_fold compress _ _ _ hbound, hb,
    ← compress.append initialWords completed _ hwhole hw]
  simp [List.append_assoc]

/-- The challenge byte order already proved from the caller is preserved all
the way through final padding and digest serialization. -/
theorem finalize_transcript (compress : Compression) (r a : BitVec 256)
    (message completed pending : Bytes)
    (hinput : completed ++ pending = transcript r a message)
    (hwhole : completed.length % 128 = 0) (hbound : pending.length < 128) :
    finalize compress (compress.run initialWords completed) pending
      (completed.length + pending.length) = digest compress (transcript r a message) := by
  rw [finalize_eq_digest compress completed pending hwhole hbound, hinput]

/-- Two backends need agree only on a single 128-byte compression block.
This is deliberately smaller than a whole-hash equality premise. -/
def BlockCompressionAgrees (left right : Compression) : Prop :=
  ∀ state block, block.length = 128 → left.run state block = right.run state block

private theorem flatten_whole (blocks : List Bytes)
    (h : ∀ b ∈ blocks, b.length = 128) : blocks.flatten.length % 128 = 0 := by
  induction blocks with
  | nil => simp
  | cons b bs ih =>
    have hb := h b (by simp)
    have hs := ih (fun b hm => h b (by simp [hm]))
    simp only [List.flatten_cons, List.length_append]
    rw [Nat.add_mod, hb, hs]

/-- Iteration over complete blocks follows from the compression composition
law; it is not supplied as an additional execution premise. -/
theorem run_flatten (compress : Compression) (state : BitVec 512)
    (blocks : List Bytes) (h : ∀ b ∈ blocks, b.length = 128) :
    compress.run state blocks.flatten = blocks.foldl compress.run state := by
  induction blocks generalizing state with
  | nil => simp [compress.empty]
  | cons b bs ih =>
    have hb := h b (by simp)
    have hs : ∀ b ∈ bs, b.length = 128 := fun b hm => h b (by simp [hm])
    simp only [List.flatten_cons, List.foldl_cons]
    rw [compress.append state b bs.flatten (by simp [hb]) (flatten_whole bs hs)]
    exact ih _ hs

theorem fold_eq_of_block_agrees (left right : Compression)
    (hagrees : BlockCompressionAgrees left right) (state : BitVec 512)
    (blocks : List Bytes) (h : ∀ b ∈ blocks, b.length = 128) :
    blocks.foldl left.run state = blocks.foldl right.run state := by
  induction blocks generalizing state with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldl_cons]
    rw [hagrees state b (h b (by simp))]
    exact ih _ (fun b hm => h b (by simp [hm]))

/-- Cross-backend digest equality follows from a one-block compression
contract and the proved padding wrapper. No whole-hash premise appears. The
original transcript may be supplied by `hinput` in `finalize_transcript`. -/
theorem digest_eq_of_block_agrees (left right : Compression)
    (hagrees : BlockCompressionAgrees left right)
    (blocks : List Bytes) (pending : Bytes)
    (hblocks : ∀ b ∈ blocks, b.length = 128) (hpending : pending.length < 128) :
    digest left (blocks.flatten ++ pending) = digest right (blocks.flatten ++ pending) := by
  rw [← finalize_eq_digest left blocks.flatten pending (flatten_whole blocks hblocks) hpending,
    ← finalize_eq_digest right blocks.flatten pending (flatten_whole blocks hblocks) hpending]
  unfold finalize
  rw [run_flatten left initialWords blocks hblocks, run_flatten right initialWords blocks hblocks,
    fold_eq_of_block_agrees left right hagrees initialWords blocks hblocks,
    fold_eq_of_block_agrees left right hagrees _ _ (finalBlocks_whole pending _ hpending)]

end Agave.Ed25519.SHA512

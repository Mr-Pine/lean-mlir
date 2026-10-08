import SSA.Projects.Agave.Ed25519.Bridge.FiredancerEnvironmentWitness

/-! Exact caller bytes observed by the existing Firedancer argument package in
the simultaneous raw loader witness, after the fresh SHA allocation. -/
namespace Agave.Ed25519.Bridge.FiredancerEnvironmentWitness
open LeanMLIR SLLVM Firedancer Firedancer.Common

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

variable {n : Nat} (message : BitVec (8*n)) (signature : BitVec 512)
  (publicKey : BitVec 256)

private theorem caller_live (i : Nat) (hi : i < 13) :
    (firedancerWithSha (initial message signature publicKey)).mem.live? (ptr i).id =
      (initial message signature publicKey).mem.live? (ptr i).id :=
  live?_afterAlloca_of_lt hi

abbrev args (hn : n < 2^63) :=
  (input message signature publicKey hn).args (wf message signature publicKey)

theorem read_key (hn : n < 2^63) :
    readBuf (args message signature publicKey hn).pkBuf = publicKey := by
  have hk := (caller_live message signature publicKey 12 (by decide)).trans
    (publicKey_live message signature publicKey)
  dsimp only [ptr] at hk
  simp [readBuf, readBuf?, hk, ptr, Pointer.offsetInBits]

theorem read_r (hn : n < 2^63) :
    readBuf (args message signature publicKey hn).sigBuf = signature.extractLsb' 0 256 := by
  have hs := (caller_live message signature publicKey 11 (by decide)).trans
    (signature_live message signature publicKey)
  dsimp only [ptr] at hs
  simp [readBuf, readBuf?, hs, ptr, Pointer.offsetInBits]

theorem read_s (hn : n < 2^63) :
    readBuf (args message signature publicKey hn).sBuf = signature.extractLsb' 256 256 := by
  have hs := (caller_live message signature publicKey 11 (by decide)).trans
    (signature_live message signature publicKey)
  dsimp only [ptr] at hs
  simp [readBuf, readBuf?, hs, ptr, Pointer.withOffset, Pointer.offsetInBits]

theorem read_message (hn : n < 2^63) :
    bytesOf (readWord (args message signature publicKey hn).msgFits) =
      bytesOf (n := n) (message.cast (Nat.mul_comm 8 n)) := by
  have hm := (caller_live message signature publicKey 10 (by decide)).trans
    (message_live message signature publicKey)
  have hsz : (BitVec.ofNat 64 n).toNat = n := by
    change n % 2^64 = n
    apply Nat.mod_eq_of_lt
    omega
  dsimp only [ptr] at hm
  simp [bytesOf, readWord, readWord?, hm, ptr, Pointer.offsetInBits, hsz]
  funext i
  rw [BitVec.extractLsb'_setWidth_of_le (by have := i.isLt; omega)]
  rw [BitVec.extractLsb'_cast]

theorem read_key_initial (hn : n < 2^63) :
    readBuf (input message signature publicKey hn).publicKey = publicKey := by
  have hk := publicKey_live message signature publicKey
  dsimp only [ptr] at hk
  simp [readBuf, readBuf?, hk, ptr, Pointer.offsetInBits]

theorem read_signature_initial (hn : n < 2^63) :
    readWord (input message signature publicKey hn).signature = signature := by
  have hs := signature_live message signature publicKey
  dsimp only [ptr] at hs
  simp [readWord, readWord?, hs, ptr, Pointer.offsetInBits]

theorem read_message_initial (hn : n < 2^63) :
    bytesOf (readWord (input message signature publicKey hn).message) =
      bytesOf (n := n) (message.cast (Nat.mul_comm 8 n)) := by
  have hm := message_live message signature publicKey
  have hsz : (BitVec.ofNat 64 n).toNat = n := by
    change n % 2^64 = n
    apply Nat.mod_eq_of_lt
    omega
  dsimp only [ptr] at hm
  simp [bytesOf, readWord, readWord?, hm, ptr, Pointer.offsetInBits, hsz]
  funext i
  rw [BitVec.extractLsb'_setWidth_of_le (by have := i.isLt; omega)]
  rw [BitVec.extractLsb'_cast]

def packMessage (bs : List (BitVec 8)) : BitVec (8 * bs.length) :=
  BitVec.packLanes (Vector.ofFn (fun i : Fin bs.length => bs[i]))

theorem bytes_packMessage (bs : List (BitVec 8)) :
    bytesOf (n := bs.length) ((packMessage bs).cast (Nat.mul_comm 8 bs.length)) = bs := by
  simp [bytesOf, packMessage, BitVec.extractLsb'_cast, BitVec.extractLsb'_packLanes]

theorem read_message_list (bs : List (BitVec 8)) (r s a : BitVec 256)
    (hn : bs.length < 2^63) :
    bytesOf (readWord (args (packMessage bs) (s ++ r) a hn).msgFits) = bs :=
  (read_message (packMessage bs) (s ++ r) a hn).trans (bytes_packMessage bs)

theorem read_r_split (r s a : BitVec 256) (hn : n < 2^63) :
    readBuf (args message (s ++ r) a hn).sigBuf = r :=
  (read_r message (s ++ r) a hn).trans BitVec.extractLsb'_append_eq_right

theorem read_s_split (r s a : BitVec 256) (hn : n < 2^63) :
    readBuf (args message (s ++ r) a hn).sBuf = s :=
  (read_s message (s ++ r) a hn).trans BitVec.extractLsb'_append_eq_left

end Agave.Ed25519.Bridge.FiredancerEnvironmentWitness

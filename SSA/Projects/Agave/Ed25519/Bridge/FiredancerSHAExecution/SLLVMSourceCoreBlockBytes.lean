import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreEntry
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreRingMemory

/-! Concrete native-chain and input-byte observations for the outer block loop. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
open LeanMLIR SLLVM Firedancer
open Agave.Ed25519.SHA512.Spec
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem chainState_eq_unpack (m : MemoryState) (chain : Pointer)
    (hc : SmallRange m chain 64) : chainState m chain = unpack (readBits m chain 512) := by
  have h0 := readBits_add_extract m chain 64 0 64 hc (by decide) (by decide)
  have h8 := readBits_add_extract m chain 64 8 64 hc (by decide) (by decide)
  have h16 := readBits_add_extract m chain 64 16 64 hc (by decide) (by decide)
  have h24 := readBits_add_extract m chain 64 24 64 hc (by decide) (by decide)
  have h32 := readBits_add_extract m chain 64 32 64 hc (by decide) (by decide)
  have h40 := readBits_add_extract m chain 64 40 64 hc (by decide) (by decide)
  have h48 := readBits_add_extract m chain 64 48 64 hc (by decide) (by decide)
  have h56 := readBits_add_extract m chain 64 56 64 hc (by decide) (by decide)
  have hp0 : chain.withOffset 0#64 = chain := by cases chain; simp [Pointer.withOffset]
  rw [hp0] at h0
  unfold chainState unpack
  congr 1

theorem pack_chainState (m : MemoryState) (chain : Pointer)
    (hc : SmallRange m chain 64) : pack (chainState m chain) = readBits m chain 512 := by
  rw [chainState_eq_unpack m chain hc, pack_unpack]

theorem readBits_chain_splice (m : MemoryState) (chain : Pointer)
    (hc : SmallRange m chain 64) (s : State) :
    readBits (m.splice chain (pack s)) chain 512 = pack s :=
  readBits_splice_self _ hc.fits

theorem readBytes_splice_disjoint (m : MemoryState) (chain data : Pointer)
    (chainBytes dataBytes : Nat) (value : BitVec (chainBytes*8))
    (hd : Disjoint chain chainBytes data dataBytes) :
    readBytes (m.splice chain value) data dataBytes = readBytes m data dataBytes := by
  unfold readBytes
  congr 1
  apply readBits_splice_disjoint
  rcases hd with h | h | h
  · exact Or.inl h
  · right; right
    simpa only [Pointer.offsetInBits, Nat.mul_add, Nat.mul_comm] using Nat.mul_le_mul_left 8 h
  · right; left
    simpa only [Pointer.offsetInBits, Nat.mul_add, Nat.mul_comm] using Nat.mul_le_mul_left 8 h

/-- A wide native read is the list of its consecutive byte reads. -/
theorem readBytes_eq_ofFn (m : MemoryState) (data : Pointer) (n : Nat)
    (hd : SmallRange m data n) :
    readBytes m data n = List.ofFn (fun i : Fin n =>
      readBits m (data.withOffset (BitVec.ofNat 64 i.val)) 8) := by
  unfold readBytes Firedancer.Common.bytesOf
  congr 1
  funext i
  simpa only [Nat.mul_comm] using
    (readBits_add_extract m data n i.val 8 hd (by omega) (by omega)).symm

theorem readBytes_append (m : MemoryState) (data : Pointer) (n k : Nat)
    (hd : SmallRange m data (n+k)) :
    readBytes m data (n+k) =
      readBytes m data n ++ readBytes m (data.withOffset (BitVec.ofNat 64 n)) k := by
  rw [readBytes_eq_ofFn m data (n+k) hd,
    readBytes_eq_ofFn m data n (hd.mono (by omega)),
    readBytes_eq_ofFn m (data.withOffset (BitVec.ofNat 64 n)) k (hd.add (by omega)),
    List.ofFn_add]
  congr 2
  funext i
  simp [Pointer.withOffset, BitVec.ofNat_add, BitVec.add_assoc]

theorem readBytes_blocks_succ (m : MemoryState) (data : Pointer) (n : Nat)
    (hd : SmallRange m data (128 * (n+1))) :
    readBytes m data (128 * (n+1)) =
      readBytes m data 128 ++ readBytes m (data.withOffset 128#64) (128*n) := by
  have he : 128 * (n+1) = 128 + 128*n := by omega
  rw [he] at hd ⊢
  exact readBytes_append m data 128 (128*n) hd

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core

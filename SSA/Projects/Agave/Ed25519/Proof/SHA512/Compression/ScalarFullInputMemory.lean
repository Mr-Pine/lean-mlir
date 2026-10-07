import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullBase
import SSA.Projects.Agave.Ed25519.Proof.SHA512.InputByteOrder

/-! Concrete native message loads and the SHA-512 big-endian decoder. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.Challenge
open Spec

private theorem readWordNative_bytesOf (v : BitVec 1024) (i : Nat) (hi : i < 16) :
    readWordNative (bytesOf (n := 128) v) i = v.extractLsb' (64 * i) 64 := by
  simp only [readWordNative, bytesOf]
  have h0 : 8 * i < 128 := by omega
  have h1 : 8 * i + 1 < 128 := by omega
  have h2 : 8 * i + 2 < 128 := by omega
  have h3 : 8 * i + 3 < 128 := by omega
  have h4 : 8 * i + 4 < 128 := by omega
  have h5 : 8 * i + 5 < 128 := by omega
  have h6 : 8 * i + 6 < 128 := by omega
  have h7 : 8 * i + 7 < 128 := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h0, h1, h2, h3, h4, h5, h6, h7, dite_eq_left, Option.getD_some]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  grind

theorem load_readWordNative (mem : MemoryState) (data : Pointer)
    (hd : SmallRange mem data 128) (i : Nat) (hi : i < 16) :
    mem.readAt (data.add (BitVec.ofNat 64 (8 * i))) 64 =
      readWordNative (readBytes mem data 128) i := by
  rw [readBytes_eq_bytesOf mem data 128 hd, readWordNative_bytesOf _ i hi]
  have hn : 8 * i < 2 ^ 64 := by omega
  have hr := MemoryState.readAt_add_of_readAt (off := BitVec.ofNat 64 (8 * i))
    (w := 64) hd.fits (hd.no_wrap (by omega)) (by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
      omega) rfl
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at hr
  simpa only [show 8 * i * 8 = 64 * i by omega] using hr

theorem load_bswap_readWordBE (mem : MemoryState) (data : Pointer)
    (hd : SmallRange mem data 128) (i : Nat) (hi : i < 16) :
    Operation.bswap (.value (mem.readAt (data.add (BitVec.ofNat 64 (8 * i))) 64)) =
      .value (readWordBE (readBytes mem data 128) i) := by
  rw [load_readWordNative mem data hd i hi]
  exact bswap_native_readWordBE _ _

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull

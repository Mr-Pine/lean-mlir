import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.PaddingMemory
import SSA.Projects.Agave.Ed25519.Proof.SHA512.ByteOrder

namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Challenge
open Agave.Ed25519.SHA512

/-- Exact single-block padding input after the emitted length store. -/
theorem short_padding_readback (s : GlobalState) (buffer : Pointer) (pending : Bytes)
    (total : Nat) (hb : SmallRange s.mem buffer 128)
    (hbytes : readBytes s.mem buffer 128 = firstPaddingBlock pending)
    (hp : pending.length < 112) :
    readBytes (writeLength s buffer (swapBytes (BitVec.ofNat 128 (8 * total)))).mem buffer 128 =
      onlyPaddingBlock pending total := by
  rw [writeLength_bytes s buffer _ hb, swapBytes128_lengthField]
  have hprefix : readBytes s.mem buffer 112 =
      pending ++ [128] ++ List.replicate (111 - pending.length) 0 := by
    rw [← readBytes_take s.mem buffer 128 112 (by decide), hbytes, firstPaddingBlock_take112 pending hp]
  rw [hprefix]
  rfl

/-- Exact final long-path block. The entire first 112 bytes are zeroed after
first compression, so its input has no dependency on the preceding buffer. -/
theorem long_padding_readback (s : GlobalState) (buffer : Pointer) (total : Nat)
    (hb : SmallRange s.mem buffer 128) :
    readBytes (writeLength (clearPrefix s buffer) buffer
      (swapBytes (BitVec.ofNat 128 (8 * total)))).mem buffer 128 = lastPaddingBlock total := by
  rw [writeLength_bytes _ buffer _ (hb.storeAt _ _), swapBytes128_lengthField]
  have hz : readBytes (clearPrefix s buffer).mem buffer 112 = List.replicate 112 0 := by
    exact (readBytes_storeAt_self s.mem buffer 112 (smallRange_mono hb (by decide)) 0#896).trans
      (bytesOf_zero 112)
  rw [hz]
  rfl

end Agave.Ed25519.Verifier.Execution.SHA512Finalization

import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.EntryTail
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Branches

/-! Byte observations of the actual padding-buffer stores. -/
namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Challenge
open Agave.Ed25519.SHA512

set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

@[simp] theorem bytesOf_zero (n : Nat) : bytesOf (0 : BitVec (n * 8)) = List.replicate n 0 := by
  simp [bytesOf, List.ofFn_const]

/-- Clear, copy, append 0x80: the exact three stores used before branching. -/
def padBuffer (m : MemoryState) (src buffer : Pointer) (n : Nat) : MemoryState :=
  let cleared := m.storeAt buffer 0#1024
  let copied := cleared.storeAt buffer (cleared.readAt src (8 * n))
  copied.storeAt (buffer.add (BitVec.ofNat 64 n)) 128#8

theorem padBuffer_bytes (m : MemoryState) (src buffer : Pointer) (n : Nat)
    (hn : n < 128) (hs : SmallRange m src n) (hb : SmallRange m buffer 128)
    (hne : buffer.id ≠ src.id) :
    readBytes (padBuffer m src buffer n) buffer 128 =
      readBytes m src n ++ [128] ++ List.replicate (127 - n) 0 := by
  let cleared := m.storeAt buffer 0#1024
  let copied := cleared.storeAt buffer (cleared.readAt src (8 * n))
  let marked := copied.storeAt (buffer.add (BitVec.ofNat 64 n)) 128#8
  have hbc : SmallRange cleared buffer 128 := hb.storeAt _ _
  have hbp : SmallRange copied buffer 128 := hbc.storeAt _ _
  have hbm : SmallRange marked buffer 128 := hbp.storeAt _ _
  have hmarkerPrefix : (Range.of (buffer.add (BitVec.ofNat 64 n)) 8).Disjoint
      (Range.of buffer (8 * n)) := by
    simpa using smallRange_disjoint_offsets hbp (i := n) (countI := 1)
      (j := 0) (countJ := n) (by omega) (by omega) (Or.inr (by omega))
  have hprefix : readBytes marked buffer n = readBytes m src n := by
    rw [readBytes_storeAt_disjoint _ _ _ _ _ (smallRange_mono hbp (by omega)) hmarkerPrefix]
    rw [readBytes_copy _ src buffer n (hs.storeAt _ _) (smallRange_mono hbc (by omega))]
    exact readBytes_storeAt_disjoint _ _ _ _ _ hs (Or.inl hne)
  have hmarker : readBytes marked (buffer.add (BitVec.ofNat 64 n)) 1 = [128] := by
    rw [readBytes_storeAt_self _ _ 1 (smallRange_add hbp (by omega))]
    simp [bytesOf]
  have hzero : readBytes cleared buffer 128 = List.replicate 128 0 := by
    exact (readBytes_storeAt_self m buffer 128 hb 0#1024).trans (bytesOf_zero 128)
  have hsuffix0 : readBytes cleared (buffer.add (BitVec.ofNat 64 (n + 1))) (127 - n) =
      List.replicate (127 - n) 0 := by
    have hdrop := readBytes_drop cleared buffer 128 (n + 1) (by omega)
    rw [hzero] at hdrop
    simpa only [List.drop_replicate, show 128 - (n + 1) = 127 - n by omega] using hdrop.symm
  have hcopySuffix : (Range.of buffer (8 * n)).Disjoint
      (Range.of (buffer.add (BitVec.ofNat 64 (n + 1))) (8 * (127 - n))) := by
    simpa using smallRange_disjoint_offsets hbc (i := 0) (countI := n)
      (j := n + 1) (countJ := 127 - n) (by omega) (by omega) (Or.inl (by omega))
  have hmarkerSuffix : (Range.of (buffer.add (BitVec.ofNat 64 n)) 8).Disjoint
      (Range.of (buffer.add (BitVec.ofNat 64 (n + 1))) (8 * (127 - n))) := by
    exact smallRange_disjoint_offsets hbp (i := n) (countI := 1)
      (j := n + 1) (countJ := 127 - n) (by omega) (by omega) (Or.inl (by omega))
  have hsuffix : readBytes marked (buffer.add (BitVec.ofNat 64 (n + 1))) (127 - n) =
      List.replicate (127 - n) 0 := by
    rw [readBytes_storeAt_disjoint _ _ _ _ _ (smallRange_add hbp (by omega)) hmarkerSuffix,
      readBytes_storeAt_disjoint _ _ _ _ _ (smallRange_add hbc (by omega)) hcopySuffix]
    exact hsuffix0
  change readBytes marked buffer 128 = _
  rw [show 128 = n + (1 + (127 - n)) by omega, readBytes_append, readBytes_append]
  simpa [Pointer.add_add, ← BitVec.ofNat_add, List.append_assoc] using
    congrArg₂ List.append hprefix (congrArg₂ List.append hmarker hsuffix)

/-- Store the final length field after preserving exactly the first 112 bytes. -/
theorem writeLength_bytes (s : GlobalState) (buffer : Pointer) (length : BitVec 128)
    (hb : SmallRange s.mem buffer 128) :
    readBytes (writeLength s buffer length).mem buffer 128 =
      readBytes s.mem buffer 112 ++ bytesOf (n := 16) length := by
  change readBytes (s.mem.storeAt (buffer.add 112#64) length) buffer (112 + 16) = _
  rw [readBytes_append, readBytes_storeAt_self _ _ 16 (smallRange_add hb (by decide))]
  congr 1
  apply readBytes_storeAt_disjoint _ _ _ _ _ (smallRange_mono hb (by decide))
  simpa using smallRange_disjoint_offsets hb (i := 112) (countI := 16)
    (j := 0) (countJ := 112) (by decide) (by decide) (Or.inr (by decide))

theorem firstPaddingBlock_take112 (pending : Bytes) (h : pending.length < 112) :
    (firstPaddingBlock pending).take 112 =
      pending ++ [128] ++ List.replicate (111 - pending.length) 0 := by
  let bytePrefix := pending ++ [128] ++ List.replicate (111 - pending.length) 0
  have hlen : bytePrefix.length = 112 := by simp [bytePrefix]; omega
  have hsplit : firstPaddingBlock pending = bytePrefix ++ List.replicate 16 0 := by
    have hn : 127 - pending.length = (111 - pending.length) + 16 := by omega
    simp [firstPaddingBlock, bytePrefix, hn, List.replicate_add, List.append_assoc]
  rw [hsplit, ← hlen, List.take_left]

/-- The entry stores represent the semantic first padding block exactly. -/
theorem paddingState_bytes (sha : Sha512Model) (s : GlobalState)
    (src ctx buffer : Pointer) (completed pending : Bytes) (count : BitVec 8)
    (hctx : ContextRepresents sha s.mem src completed pending)
    (hc : SmallRange s.mem ctx 208) (hb : SmallRange s.mem buffer 128)
    (hne : buffer.id ≠ ctx.id) (hcount : count.toNat = pending.length) :
    readBytes (paddingState s src ctx buffer count).mem buffer 128 = firstPaddingBlock pending := by
  have hcopy := ContextRepresents.copy sha s.mem src ctx completed pending hctx hc
  have hsource : SmallRange (cloned s src ctx).mem ctx count.toNat :=
    smallRange_mono hcopy.live (by rw [hcount]; have := hctx.pendingBound; omega)
  have hbuffer : SmallRange (cloned s src ctx).mem buffer 128 := hb.storeAt _ _
  have h := padBuffer_bytes (cloned s src ctx).mem ctx buffer count.toNat
    (by rw [hcount]; exact hctx.pendingBound) hsource hbuffer hne
  have h' : readBytes (paddingState s src ctx buffer count).mem buffer 128 =
      readBytes (cloned s src ctx).mem ctx count.toNat ++ [128] ++
        List.replicate (127 - count.toNat) 0 := by
    simpa only [paddingState, paddingCopied, paddingCleared, padBuffer, BitVec.ofNat_toNat] using h
  rw [h', hcount]
  change readBytes (s.mem.storeAt ctx (s.mem.readAt src 1664)) ctx pending.length ++
    [128] ++ List.replicate (127 - pending.length) 0 = _
  rw [hcopy.pendingBytes]
  rfl

end Agave.Ed25519.Verifier.Execution.SHA512Finalization

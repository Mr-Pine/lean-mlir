import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Field

/-! Byte-memory readback for the overlapping loads in the actual decoder entry.
These memory facts connect its load/mask expressions to the proved parser. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

theorem input_part (s : GlobalState) (input : Pointer) (bytes : BitVec 256)
    (hinput : SmallRange s.mem input 32) (hbytes : s.mem.readAt input 256 = bytes)
    (offset width : Nat) (hpart : offset * 8 + width ≤ 256) :
    s.mem.readAt (input.add (BitVec.ofNat 64 offset)) width =
      bytes.extractLsb' (offset * 8) width := by
  have hoff : offset ≤ 32 := by omega
  have hoff64 : offset < 18446744073709551616 := by omega
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff64] using
    (MemoryState.readAt_add_of_readAt (w := width) hinput.fits (hinput.no_wrap hoff)
      (by simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff64] using hpart) hbytes)

/-- Precisely the decoder's five unaligned i64 loads, shifts and masks. -/
def inputWords (s : GlobalState) (input : Pointer) : Words := ![
  s.mem.readAt input 64 &&& 2251799813685247,
  (s.mem.readAt (input.add 6#64) 64 >>> 3) &&& 2251799813685247,
  (s.mem.readAt (input.add 12#64) 64 >>> 6) &&& 2251799813685247,
  (s.mem.readAt (input.add 19#64) 64 >>> 1) &&& 2251799813685247,
  (s.mem.readAt (input.add 24#64) 64 >>> 12) &&& 2251799813685247]

theorem inputWords_eq (s : GlobalState) (input : Pointer) (bytes : BitVec 256)
    (hinput : SmallRange s.mem input 32) (hbytes : s.mem.readAt input 256 = bytes) :
    inputWords s input = fromBytesWord bytes := by
  have h0 := input_part s input bytes hinput hbytes 0 64 (by decide)
  have h6 := input_part s input bytes hinput hbytes 6 64 (by decide)
  have h12 := input_part s input bytes hinput hbytes 12 64 (by decide)
  have h19 := input_part s input bytes hinput hbytes 19 64 (by decide)
  have h24 := input_part s input bytes hinput hbytes 24 64 (by decide)
  simp only [Pointer.add_zero, Nat.zero_mul] at h0
  norm_num only [Nat.cast_ofNat, Nat.reduceMul] at h6 h12 h19 h24
  simp only [inputWords, fromBytesWord, h0, h6, h12, h19, h24]

/-- All input bytes give a tightly bounded field element through the actual
load expressions, without a canonical-y or curve-membership assumption. -/
theorem inputWords_contract (s : GlobalState) (input : Pointer) (bytes : BitVec 256)
    (hinput : SmallRange s.mem input 32) (hbytes : s.mem.readAt input 256 = bytes) :
    wordValue (inputWords s input) = y bytes ∧
      SerialPoint.Tight (SerialFieldMul.unsigned (inputWords s input)) := by
  rw [inputWords_eq s input bytes hinput hbytes]
  exact ⟨fromBytesWord_value bytes, fromBytesWord_tight bytes⟩

end Agave.Ed25519.Encoding.Decompress.Execution

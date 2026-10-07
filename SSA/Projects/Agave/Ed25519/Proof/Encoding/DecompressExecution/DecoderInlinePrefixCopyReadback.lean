import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixSuccess

/-! Whole-field observations through the original post-sqrt copies. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
open LeanMLIR.RIR SerialFieldMul
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000

theorem payload_extract (bits : BitVec 320) :
    fieldPayload (fun i : Fin 5 => bits.extractLsb' (64 * i.val) 64) = bits := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [fieldPayload,BitVec.getLsbD_append,BitVec.getLsbD_extractLsb']
  grind

theorem payload_readLimbs (s : GlobalState) (p : Pointer) (hp : SmallRange s.mem p 40) :
    fieldPayload (readLimbs s p) = s.mem.readAt p 320 := by
  have he : readLimbs s p = fun i : Fin 5 => (s.mem.readAt p 320).extractLsb' (64 * i.val) 64 := by
    funext i
    have hb : 8 * i.val < 18446744073709551616 := by omega
    have hr := MemoryState.readAt_add_of_readAt (off := BitVec.ofNat 64 (8 * i.val))
      (w := 64) hp.fits (hp.no_wrap (k := 8 * i.val) (by omega))
      (by simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hb]; omega)
      (rfl : s.mem.readAt p 320 = _)
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hb] at hr
    simpa only [readLimbs,
      Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hr
  rw [he,payload_extract]

theorem sqrtInput_parsed (g : Globals) (s : GlobalState) (input : Pointer)
    (bytes : BitVec 256) (hwf : s.WF)
    (hin : Verifier.Execution.Dalek.ReadBytes s input 32 bytes) :
    readLimbs (sqrtInputState g s input) (slot5 s) = (parsedWord bytes).limbs := by
  unfold sqrtInputState
  rw [denominator_read_ne _ _ _ _
    (by intro h; have := congrArg BlockId.id h; simp only [slot2_id,slot5_id] at this; omega)]
  unfold productState
  rw [readLimbs_storeLimbs_ne _ _ _ _
    (by intro h; have := congrArg BlockId.id h; simp only [slot1_id,slot5_id] at this; omega)]
  unfold numeratorState
  rw [carry_result_read_ne _ _ _ _
    (by intro h; have := congrArg BlockId.id h; simp only [slot3_id,slot5_id] at this; omega)]
  unfold squareState
  rw [readLimbs_storeLimbs_ne _ _ _ _
    (by intro h; have := congrArg BlockId.id h; simp only [slot4_id,slot5_id] at this; omega)]
  exact parse_readback s input bytes hwf hin

theorem sqrtInput_parsed320 (g : Globals) (s : GlobalState) (input : Pointer)
    (bytes : BitVec 256) (hwf : s.WF)
    (hin : Verifier.Execution.Dalek.ReadBytes s input 32 bytes) :
    (sqrtInputState g s input).mem.readAt (slot5 s) 320 = fieldPayload (parsedWord bytes).limbs := by
  rw [← payload_readLimbs _ _ (sqrtInput_live g s input _ _ (slot5_live s hwf)),
    sqrtInput_parsed g s input bytes hwf hin]

theorem copied_pair_x (s t : GlobalState) (h7 : SmallRange t.mem (slot7 s) 80) :
    (copiedPairState s t).mem.readAt (slot7 s) 320 = t.mem.readAt ((slot0 s).add 8#64) 320 := by
  have hf := h7.fits_add (k := 0) (count := 40) (by decide)
  simp only [Pointer.add_zero] at hf
  have ho := Pointer.offsetInBits_add (h7.no_wrap (k := 40) (by decide))
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod] at ho
  have hd : (Range.of ((slot7 s).add 40#64) 320).Disjoint (Range.of (slot7 s) 320) := by
    simp only [Range.Disjoint,Range.of,Pointer.add_id,ho]
    omega
  change (((copiedRootState s t).mem.storeAt ((slot7 s).add 40#64) _).readAt (slot7 s) 320) = _
  rw [MemoryState.readAt_storeAt_disjoint hd]
  exact MemoryState.readAt_storeAt_self hf _

theorem copied_pair_y (s t : GlobalState) (h7 : SmallRange t.mem (slot7 s) 80) :
    (copiedPairState s t).mem.readAt ((slot7 s).add 40#64) 320 = t.mem.readAt (slot5 s) 320 := by
  have hf := h7.fits_add (k := 40) (count := 40) (by decide)
  change (((copiedRootState s t).mem.storeAt ((slot7 s).add 40#64) _).readAt ((slot7 s).add 40#64) 320) = _
  have hf' : Fits (copiedRootState s t).mem ((slot7 s).add 40#64) 320 := hf.storeAt
  rw [MemoryState.readAt_storeAt_self hf']
  exact MemoryState.readAt_storeAt_disjoint
    (p := slot7 s) (q := slot5 s) (m := t.mem) (v := 320) (w := 320)
    (Or.inl (by intro h; have := congrArg BlockId.id h; simp only [Range.of,slot7_id,slot5_id] at this; omega)) _

theorem copied_x_readback (s t : GlobalState)
    (h7 : SmallRange t.mem (slot7 s) 80) (h9 : SmallRange t.mem (slot9 s) 40) :
    (copiedXYState s t).mem.readAt (slot9 s) 320 = t.mem.readAt ((slot0 s).add 8#64) 320 := by
  change (((copiedXState s t).mem.storeAt (slot8 s) _).readAt (slot9 s) 320) = _
  rw [MemoryState.readAt_storeAt_disjoint (p := slot8 s) (q := slot9 s) (w := 320)
    (Or.inl (by intro h; have := congrArg BlockId.id h; simp only [Range.of,slot8_id,slot9_id] at this; omega))]
  change (((copiedPairState s t).mem.storeAt (slot9 s) _).readAt (slot9 s) 320) = _
  have hf : Fits (copiedPairState s t).mem (slot9 s) 320 := h9.fits.storeAt.storeAt
  rw [MemoryState.readAt_storeAt_self hf]
  exact copied_pair_x s t h7

theorem copied_y_readback (s t : GlobalState)
    (h7 : SmallRange t.mem (slot7 s) 80) (h8 : SmallRange t.mem (slot8 s) 40) :
    (copiedXYState s t).mem.readAt (slot8 s) 320 = t.mem.readAt (slot5 s) 320 := by
  change (((copiedXState s t).mem.storeAt (slot8 s) _).readAt (slot8 s) 320) = _
  have hf : Fits (copiedXState s t).mem (slot8 s) 320 := h8.fits.storeAt.storeAt.storeAt
  rw [MemoryState.readAt_storeAt_self hf]
  change (((copiedPairState s t).mem.storeAt (slot9 s) _).readAt ((slot7 s).add 40#64) 320) = _
  rw [MemoryState.readAt_storeAt_disjoint (p := slot9 s) (q := (slot7 s).add 40#64) (w := 320)
    (Or.inl (by intro h; have := congrArg BlockId.id h; simp only [Range.of,Pointer.add_id,slot9_id,slot7_id] at this; omega))]
  exact copied_pair_y s t h7

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix

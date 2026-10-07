import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixCopyReadback
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderSemantic

/-! Exact X/Y/T observations after all fifty original success instructions. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
open LeanMLIR.RIR SerialFieldMul
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
attribute [local irreducible] machine

theorem pointX_read_ne (s : GlobalState) (point x q : Pointer) (hd : point.id ≠ q.id) :
    readLimbs (pointXState s point x) q = readLimbs s q := by
  funext i
  exact MemoryState.readAt_storeAt_disjoint (p := point)
    (q := q.add (BitVec.ofNat 64 (8 * i.val))) (m := s.mem) (v := 320) (w := 64) (Or.inl hd) _

theorem pointT_x_read (s : GlobalState) (point x y : Pointer)
    (hp : SmallRange s.mem point 160) :
    (pointTState s point x y).mem.readAt point 320 = s.mem.readAt x 320 := by
  have ht : SmallRange (pointXState s point x).mem (point.add 120#64) 40 :=
    smallRange_add (hp.storeAt _ _) (k := 120) (count := 40) (by decide)
  have ho := Pointer.offsetInBits_add (hp.no_wrap (k := 120) (by decide))
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod] at ho
  have hd : (Range.of point 320).Disjoint (Range.of (point.add 120#64) 320) := by
    simp only [Range.Disjoint,Range.of,Pointer.add_id,ho]
    omega
  unfold pointTState
  rw [readAt_storeLimbs_frame _ _ _ _ _ ht hd]
  exact MemoryState.readAt_storeAt_self (Fits.mono (by decide : 320 ≤ 1280) hp.fits) _

theorem pointT_y_read (s : GlobalState) (point x y : Pointer) (hd : point.id ≠ y.id) :
    (pointTState s point x y).mem.readAt y 320 = s.mem.readAt y 320 := by
  unfold pointTState
  rw [readAt_storeLimbs_ne _ (point.add 120#64) y _ 320 hd]
  exact MemoryState.readAt_storeAt_disjoint (p := point) (q := y) (m := s.mem)
    (v := 320) (w := 320) (Or.inl hd) _

theorem pointT_t_read (s : GlobalState) (point x y : Pointer)
    (hp : SmallRange s.mem point 160) (hdx : point.id ≠ x.id) (hdy : point.id ≠ y.id) :
    (pointTState s point x y).mem.readAt (point.add 120#64) 320 =
      fieldPayload (machine (readLimbs s x) (readLimbs s y)) := by
  have ht : SmallRange (pointXState s point x).mem (point.add 120#64) 40 :=
    smallRange_add (hp.storeAt _ _) (k := 120) (count := 40) (by decide)
  unfold pointTState
  rw [storeLimbs_read320 _ _ _ ht,pointX_read_ne s point x x hdx,pointX_read_ne s point x y hdy]
  rfl

theorem success_sign_bit (q : GlobalState) (input : Pointer) (bytes : BitVec 256)
    (hin : Verifier.Execution.Dalek.ReadBytes q input 32 bytes) :
    (successByte q input)[7] = bytes[255] := by
  have hb := MemoryState.readAt_add_of_readAt (off := 31#64) (w := 8)
    hin.1.fits (hin.1.no_wrap (k := 31) (by decide)) (by decide) hin.2
  change successByte q input = bytes.extractLsb' 248 8 at hb
  rw [hb]
  simp only [BitVec.getElem_extractLsb']
  rfl

theorem success_words (s q : GlobalState) (input : Pointer) (bytes : BitVec 256)
    (root : Pow22501.TightWords) (hin : Verifier.Execution.Dalek.ReadBytes q input 32 bytes)
    (h6 : SmallRange q.mem (slot6 s) 160) (h8 : SmallRange q.mem (slot8 s) 40)
    (h9 : SmallRange q.mem (slot9 s) 40)
    (hroot : readLimbs q (slot9 s) = root.limbs)
    (hy : readLimbs q (slot8 s) = (parsedWord bytes).limbs) :
    (successPrefixState s q input).mem.readAt (slot6 s) 320 =
        fieldPayload (pointWords bytes root).X.limbs ∧
      (successPrefixState s q input).mem.readAt (slot8 s) 320 =
        fieldPayload (pointWords bytes root).Y.limbs ∧
      (successPrefixState s q input).mem.readAt ((slot6 s).add 120#64) 320 =
        fieldPayload (pointWords bytes root).T.limbs := by
  have hd68 : (slot6 s).id ≠ (slot8 s).id := by
    intro h; have := congrArg BlockId.id h; simp only [slot6_id,slot8_id] at this; omega
  have hd69 : (slot6 s).id ≠ (slot9 s).id := by
    intro h; have := congrArg BlockId.id h; simp only [slot6_id,slot9_id] at this; omega
  have hd98 : (slot9 s).id ≠ (slot8 s).id := by
    intro h; have := congrArg BlockId.id h; simp only [slot9_id,slot8_id] at this; omega
  have hx : readLimbs (successSignedState s q input) (slot9 s) =
      signedWords bytes[255] root.limbs := by
    unfold successSignedState
    rw [signed_readback (signState q) (slot9 s) (successByte q input) h9]
    change signedWords (successByte q input)[7] (readLimbs q (slot9 s)) = _
    rw [success_sign_bit q input bytes hin,hroot]
  have hy' : readLimbs (successSignedState s q input) (slot8 s) = (parsedWord bytes).limbs := by
    have he : readLimbs (successSignedState s q input) (slot8 s) = readLimbs q (slot8 s) := by
      funext i
      exact signed_read_ne (signState q) (slot9 s)
        ((slot8 s).add (BitVec.ofNat 64 (8 * i.val))) (successByte q input) 64 hd98
    exact he.trans hy
  constructor
  · unfold successPrefixState
    rw [pointT_x_read _ _ _ _ (success_signed_live s q input _ h6),
      ← payload_readLimbs _ _ (success_signed_live s q input _ h9),hx]
    rfl
  constructor
  · unfold successPrefixState
    rw [pointT_y_read _ _ _ _ hd68,
      ← payload_readLimbs _ _ (success_signed_live s q input _ h8),hy']
    rfl
  · unfold successPrefixState
    rw [pointT_t_read _ _ _ _ (success_signed_live s q input _ h6) hd69 hd68,hx,hy']
    rfl

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix

import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekIdentityMemory

/-! Caller-visible Option layout of the exact decompressor. Payload bits are
kept exact: this layer imposes no canonical representation of field elements. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open Verifier.Execution.Dalek (ReadBytes OutputFrame smallRange_add disjoint_add_subrange)

/-- The success path's last memcpy, followed by the common tag store. -/
def successState (s : GlobalState) (out : Pointer) (payload : BitVec 1280) : GlobalState :=
  {s with mem := (s.mem.storeAt (out.add 8#64) payload).storeAt out (1#64)}

/-- Rejection does not require an initialized point payload. -/
def rejectionState (s : GlobalState) (out : Pointer) : GlobalState :=
  {s with mem := s.mem.storeAt out (0#64)}

theorem successState_live (h : SmallRange s.mem q bytes) (out : Pointer)
    (payload : BitVec 1280) : SmallRange (successState s out payload).mem q bytes :=
  (h.storeAt _ _).storeAt _ _

theorem rejectionState_live (h : SmallRange s.mem q bytes) (out : Pointer) :
    SmallRange (rejectionState s out).mem q bytes := h.storeAt _ _

private theorem tag_payload_disjoint {s : GlobalState} {out : Pointer}
    (h : SmallRange s.mem out 168) :
    (Range.of out 64).Disjoint (Range.of (out.add 8#64) 1280) := by
  have ho := Pointer.offsetInBits_add (h.no_wrap (k := 8) (by decide))
  norm_num only [Nat.cast_ofNat, BitVec.toNat_ofNat, Nat.reduceMod] at ho
  simp only [Range.Disjoint, Range.of, Pointer.add_id, ho]
  omega

theorem successState_tag (h : SmallRange s.mem out 168) (payload : BitVec 1280) :
    (successState s out payload).mem.readAt out 64 = 1#64 := by
  have hf : Fits s.mem out 64 := Fits.mono (by decide) h.fits
  exact MemoryState.readAt_storeAt_self hf.storeAt _

theorem rejectionState_tag (h : SmallRange s.mem out 168) :
    (rejectionState s out).mem.readAt out 64 = 0#64 :=
  MemoryState.readAt_storeAt_self (Fits.mono (by decide) h.fits) _

theorem successState_payload (h : SmallRange s.mem out 168) (payload : BitVec 1280) :
    ReadBytes (successState s out payload) (out.add 8#64) 160 payload := by
  have hp : SmallRange s.mem (out.add 8#64) 160 :=
    smallRange_add h (k := 8) (by decide)
  refine ⟨(hp.storeAt _ _).storeAt _ _, ?_⟩
  change ((s.mem.storeAt (out.add 8#64) payload).storeAt out (1#64)).readAt
    (out.add 8#64) 1280 = payload
  rw [MemoryState.readAt_storeAt_disjoint (tag_payload_disjoint h)]
  exact MemoryState.readAt_storeAt_self hp.fits payload

theorem successState_frame (hwf : s.WF) (h : SmallRange s.mem out 168)
    (payload : BitVec 1280) : OutputFrame s (successState s out payload) out 168 := by
  constructor
  · simpa only [successState, GlobalState.WF_storeAt] using hwf
  · intro q n hq
    exact successState_live hq out payload
  · intro q w hd
    have htag := disjoint_add_subrange h hd (k := 0) (count := 8) (by decide)
    have hpoint := disjoint_add_subrange h hd (k := 8) (count := 160) (by decide)
    simp only [Pointer.add_zero] at htag
    simp only [successState, MemoryState.readAt_storeAt_disjoint htag.symm,
      MemoryState.readAt_storeAt_disjoint hpoint.symm]

theorem rejectionState_frame (hwf : s.WF) (h : SmallRange s.mem out 168) :
    OutputFrame s (rejectionState s out) out 168 := by
  constructor
  · simpa only [rejectionState, GlobalState.WF_storeAt] using hwf
  · intro q n hq
    exact rejectionState_live hq out
  · intro q w hd
    have htag := disjoint_add_subrange h hd (k := 0) (count := 8) (by decide)
    simp only [Pointer.add_zero] at htag
    exact MemoryState.readAt_storeAt_disjoint htag.symm (0#64)

/-- Every caller read inside the payload follows from its complete byte read.
This includes overlapping vector loads and needs no limb canonicality. -/
theorem payload_part (s : GlobalState) (out : Pointer) (payload : BitVec 1280)
    (hread : ReadBytes s (out.add 8#64) 160 payload)
    (k width : Nat) (hk : k ≤ 160) (hwidth : 8 * k + width ≤ 1280) :
    s.mem.readAt (out.add (BitVec.ofNat 64 (8 + k))) width =
      payload.extractLsb' (8 * k) width := by
  have hk64 : k < 18446744073709551616 := by omega
  have hb : (BitVec.ofNat 64 k).toNat * 8 + width ≤ 1280 := by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64, Nat.mul_comm] using hwidth
  have hr := MemoryState.readAt_add_of_readAt (w := width) hread.1.fits
    (hread.1.no_wrap hk) hb hread.2
  rw [Pointer.add_add, ← BitVec.ofNat_add] at hr
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64, Nat.mul_comm] using hr

/-- Exact six vector reads required by the key-construction caller. -/
structure KeyChunks (s : GlobalState) (out : Pointer) (payload : BitVec 1280) : Prop where
  x0 : s.mem.readAt (out.add 8#64) 128 = payload.extractLsb' 0 128
  x8 : s.mem.readAt (out.add 16#64) 128 = payload.extractLsb' 64 128
  x24 : s.mem.readAt (out.add 32#64) 128 = payload.extractLsb' 192 128
  t0 : s.mem.readAt (out.add 128#64) 128 = payload.extractLsb' 960 128
  t8 : s.mem.readAt (out.add 136#64) 128 = payload.extractLsb' 1024 128
  t24 : s.mem.readAt (out.add 152#64) 128 = payload.extractLsb' 1152 128

theorem keyChunks_of_payload (s : GlobalState) (out : Pointer) (payload : BitVec 1280)
    (hread : ReadBytes s (out.add 8#64) 160 payload) : KeyChunks s out payload := by
  constructor
  · simpa using payload_part s out payload hread 0 128 (by decide) (by decide)
  · simpa using payload_part s out payload hread 8 128 (by decide) (by decide)
  · simpa using payload_part s out payload hread 24 128 (by decide) (by decide)
  · simpa using payload_part s out payload hread 120 128 (by decide) (by decide)
  · simpa using payload_part s out payload hread 128 128 (by decide) (by decide)
  · simpa using payload_part s out payload hread 144 128 (by decide) (by decide)

theorem successState_keyChunks (h : SmallRange s.mem out 168) (payload : BitVec 1280) :
    KeyChunks (successState s out payload) out payload :=
  keyChunks_of_payload _ _ _ (successState_payload h payload)

end Agave.Ed25519.Encoding.Decompress.Execution.Decode

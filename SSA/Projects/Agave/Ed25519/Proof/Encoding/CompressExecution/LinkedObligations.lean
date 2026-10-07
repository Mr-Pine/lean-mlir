import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.LinkedPow22501
import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.ScratchMemory
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekCompressPrimitive

/-! Construct every primitive boundary from actual linked helper executions.
Only readable input/output memory and tight input coordinates are premises. -/
namespace Agave.Ed25519.Encoding.Compress.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open SerialFieldMul (readLimbs storeLimbs unsigned)
open SerialPoint.Execution

private theorem limbs_mem_congr {s t : GlobalState} (h : s.mem = t.mem) (p : Pointer) :
    readLimbs s p = readLimbs t p := by
  funext i
  change s.mem.readAt _ 64 = t.mem.readAt _ 64
  rw [h]

private theorem limbs_store_readback {s t : GlobalState} {dst : Pointer} {v : Field.Serial}
    (h : t.mem = storeLimbs s.mem dst v)
    (hd : SmallRange s.mem dst 40) : readLimbs t dst = v :=
  (limbs_mem_congr h dst).trans (readLimbs_storeLimbs s dst v hd)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem linked_primitive_obligations (out input : Pointer) (initial : GlobalState)
    (hwf : initial.WF) (hout : SmallRange initial.mem out 32)
    (hin : SmallRange initial.mem input 160)
    (hx : SerialPoint.Tight (unsigned (readLimbs initial input)))
    (hy : SerialPoint.Tight (unsigned (readLimbs initial (input.add 40))))
    (hz : SerialPoint.Tight (unsigned (readLimbs initial (input.add 80)))) :
    ∃ states afterBlack words,
      Verifier.Execution.Dalek.CompressPrimitiveObligations linkedPrimitives
        initial afterBlack input out states words := by
  let allocated := scratchState initial 6
  have hawf : allocated.WF := scratchState_wf hwf 6
  have halive (p : Pointer) (n : Nat) (h : SmallRange initial.mem p n) :
      SmallRange allocated.mem p n := scratchState_live hwf h 6
  have hslot (i : Nat) (hi : i < 6) :
      SmallRange allocated.mem (scratch initial i) (scratchBytes i) := scratch_live hwf hi
  have hinput := halive input 160 hin
  have hinputX : SmallRange initial.mem input 40 := by
    simpa only [Pointer.add_zero] using smallRange_add hin (k := 0) (count := 40) (by decide)
  have hinputY : SmallRange initial.mem (input.add 40) 40 :=
    smallRange_add hin (k := 40) (count := 40) (by decide)
  have hinputZ : SmallRange initial.mem (input.add 80) 40 :=
    smallRange_add hin (k := 80) (count := 40) (by decide)
  have hreadA (p : Pointer) (h : SmallRange initial.mem p 40) :
      readLimbs allocated p = readLimbs initial p := scratchState_readLimbs hwf h 6
  have hold (i : Nat) (p : Pointer) (h : SmallRange initial.mem p 40) :
      (scratch initial i).id ≠ p.id := scratch_ne_old hwf h.fits i
  have hn (i j : Nat) (h : i ≠ j) : (scratch initial i).id ≠ (scratch initial j).id :=
    scratch_ne initial h
  have hp1 : SmallRange allocated.mem (scratch initial 1) 80 := hslot 1 (by decide)
  obtain ⟨powed, first, second, hpcall, hpmem, hpwf, hpcounter, hpv1, hpv2, hpt1, hpt2⟩ :=
    linked_pow22501_contract (scratch initial 1) (input.add 80) allocated hawf hp1
      (halive _ _ hinputZ) (by rw [hreadA _ hinputZ]; exact hz)
  have hplive (p : Pointer) (n : Nat) (h : SmallRange allocated.mem p n) :
      SmallRange powed.mem p n := by
    rw [hpmem]
    exact smallRange_storeLimbs (smallRange_storeLimbs h _ first) _ second
  have hpair := hplive _ _ hp1
  have hfirst := hplive _ _ (hslot 3 (by decide))
  have hsecond := hplive _ _ (hslot 2 (by decide))
  have hp1first : SmallRange allocated.mem (scratch initial 1) 40 := by
    simpa only [Pointer.add_zero] using smallRange_add hp1 (k := 0) (count := 40) (by decide)
  have hp1second : SmallRange allocated.mem ((scratch initial 1).add 40) 40 :=
    smallRange_add hp1 (k := 40) (count := 40) (by decide)
  have hd12 : (Range.of (scratch initial 1) 320).Disjoint
      (Range.of ((scratch initial 1).add 40) 320) := by
    have hoff := Pointer.offsetInBits_add (hp1.no_wrap (k := 40) (by decide))
    simp only [Range.Disjoint, Range.of, Pointer.add_id]
    exact Or.inr (Or.inl (le_of_eq (by
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul]
        using hoff.symm)))
  have hpowReadFirst : readLimbs powed (scratch initial 1) = first := by
    exact (limbs_mem_congr (s := powed)
      (t := {allocated with mem := storeLimbs (storeLimbs allocated.mem (scratch initial 1) first) ((scratch initial 1).add 40) second}) hpmem _).trans
      ((readLimbs_storeLimbs_frame {allocated with mem := storeLimbs allocated.mem (scratch initial 1) first} ((scratch initial 1).add 40) (scratch initial 1) second
        (smallRange_storeLimbs hp1second _ first)
        (smallRange_storeLimbs hp1first _ first) hd12).trans
        (readLimbs_storeLimbs allocated _ first hp1first))
  have hpowReadSecond : readLimbs powed ((scratch initial 1).add 40) = second :=
    limbs_store_readback
      (s := {allocated with mem := storeLimbs allocated.mem (scratch initial 1) first})
      hpmem (smallRange_storeLimbs hp1second _ first)
  have hpowReadOld (p : Pointer) (hp : SmallRange initial.mem p 40) :
      readLimbs powed p = readLimbs initial p := by
    exact (limbs_mem_congr (s := powed)
      (t := {allocated with mem := storeLimbs (storeLimbs allocated.mem (scratch initial 1) first) ((scratch initial 1).add 40) second}) hpmem p).trans
      ((readLimbs_storeLimbs_ne {allocated with mem := storeLimbs allocated.mem (scratch initial 1) first} ((scratch initial 1).add 40) p second (hold 1 p hp)).trans
        ((readLimbs_storeLimbs_ne allocated (scratch initial 1) p first (hold 1 p hp)).trans (hreadA p hp)))
  let copied := copySecond initial powed
  have hcwf : copied.WF := copySecond_wf hpwf
  have hclive (p : Pointer) (n : Nat) (h : SmallRange allocated.mem p n) :
      SmallRange copied.mem p n := copySecond_live (hplive p n h)
  have hcopyFirst : readLimbs copied (scratch initial 3) = first :=
    (copySecond_first_readback hfirst (hplive _ _ hp1first)).trans hpowReadFirst
  have hcopySecond : readLimbs copied (scratch initial 2) = second :=
    (copySecond_readback hsecond (hplive _ _ hp1second)).trans hpowReadSecond
  have hcopyOld (p : Pointer) (hp : SmallRange initial.mem p 40) :
      readLimbs copied p = readLimbs initial p :=
    (copySecond_readLimbs_frame (hold 2 p hp) (hold 3 p hp)).trans (hpowReadOld p hp)
  obtain ⟨squaredWords, hscall, hsv, hst⟩ := linked_pow2k5_call (scratch initial 0)
    (scratch initial 3) copied hcwf (hclive _ _ (hslot 0 (by decide)))
      (hclive _ _ (hslot 3 (by decide))) (by rw [hcopyFirst]; exact hpt1)
  let squared : GlobalState := {copied with mem := storeLimbs copied.mem (scratch initial 0) squaredWords}
  have hswf : squared.WF := wf_storeLimbs hcwf _ _
  have hslive (p : Pointer) (n : Nat) (h : SmallRange allocated.mem p n) :
      SmallRange squared.mem p n := smallRange_storeLimbs (hclive p n h) _ _
  have hsread : readLimbs squared (scratch initial 0) = squaredWords :=
    readLimbs_storeLimbs copied _ _ (hclive _ _ (hslot 0 (by decide)))
  have hssecond : readLimbs squared (scratch initial 2) = second :=
    (readLimbs_storeLimbs_ne copied (scratch initial 0) (scratch initial 2) squaredWords (hn 0 2 (by decide))).trans hcopySecond
  have hsold (p : Pointer) (hp : SmallRange initial.mem p 40) :
      readLimbs squared p = readLimbs initial p :=
    (readLimbs_storeLimbs_ne copied (scratch initial 0) p squaredWords (hold 0 p hp)).trans (hcopyOld p hp)
  obtain ⟨inverse, hicall, hiv, hit⟩ := linked_mul_call (scratch initial 4)
    (scratch initial 0) (scratch initial 2) squared hswf
      (hslive _ _ (hslot 4 (by decide))) (hslive _ _ (hslot 0 (by decide)))
      (hslive _ _ (hslot 2 (by decide)))
      (by rw [hsread]; exact SerialPoint.tight_bounded _ hst)
      (by rw [hssecond]; exact SerialPoint.tight_bounded _ hpt2)
  let inverted : GlobalState := {squared with mem := storeLimbs squared.mem (scratch initial 4) inverse}
  have hiwf : inverted.WF := wf_storeLimbs hswf _ _
  have hilive (p : Pointer) (n : Nat) (h : SmallRange allocated.mem p n) :
      SmallRange inverted.mem p n := smallRange_storeLimbs (hslive p n h) _ _
  have hiread : readLimbs inverted (scratch initial 4) = inverse :=
    readLimbs_storeLimbs squared _ _ (hslive _ _ (hslot 4 (by decide)))
  have hiold (p : Pointer) (hp : SmallRange initial.mem p 40) :
      readLimbs inverted p = readLimbs initial p :=
    (readLimbs_storeLimbs_ne squared (scratch initial 4) p inverse (hold 4 p hp)).trans (hsold p hp)
  have hxslot : SmallRange allocated.mem (scratch initial 5) 40 := by
    simpa only [Pointer.add_zero] using smallRange_add (hslot 5 (by decide))
      (k := 0) (count := 40) (by decide)
  have hyslot : SmallRange allocated.mem ((scratch initial 5).add 40) 40 :=
    smallRange_add (hslot 5 (by decide)) (k := 40) (count := 40) (by decide)
  obtain ⟨affineX, hxcall, hxv, hxt⟩ := linked_mul_call (scratch initial 5) input
    (scratch initial 4) inverted hiwf (hilive _ _ hxslot) (hilive _ _ (halive _ _ hinputX))
      (hilive _ _ (hslot 4 (by decide)))
      (by rw [hiold _ hinputX]; exact SerialPoint.tight_bounded _ hx)
      (by rw [hiread]; exact SerialPoint.tight_bounded _ hit)
  let xState : GlobalState := {inverted with mem := storeLimbs inverted.mem (scratch initial 5) affineX}
  have hxwf : xState.WF := wf_storeLimbs hiwf _ _
  have hxlive (p : Pointer) (n : Nat) (h : SmallRange allocated.mem p n) :
      SmallRange xState.mem p n := smallRange_storeLimbs (hilive p n h) _ _
  have hxinv : readLimbs xState (scratch initial 4) = inverse :=
    (readLimbs_storeLimbs_ne inverted (scratch initial 5) (scratch initial 4) affineX (hn 5 4 (by decide))).trans hiread
  have hxyread : readLimbs xState (input.add 40) = readLimbs initial (input.add 40) :=
    (readLimbs_storeLimbs_ne inverted (scratch initial 5) (input.add 40) affineX (hold 5 _ hinputY)).trans (hiold _ hinputY)
  obtain ⟨affineY, hycall, hyv, hyt⟩ := linked_mul_call ((scratch initial 5).add 40)
    (input.add 40) (scratch initial 4) xState hxwf (hxlive _ _ hyslot)
      (hxlive _ _ (halive _ _ hinputY)) (hxlive _ _ (hslot 4 (by decide)))
      (by rw [hxyread]; exact SerialPoint.tight_bounded _ hy)
      (by rw [hxinv]; exact SerialPoint.tight_bounded _ hit)
  let xyState : GlobalState := {xState with mem := storeLimbs xState.mem ((scratch initial 5).add 40) affineY}
  have hxywf : xyState.WF := wf_storeLimbs hxwf _ _
  have hxylive (p : Pointer) (n : Nat) (h : SmallRange allocated.mem p n) :
      SmallRange xyState.mem p n := smallRange_storeLimbs (hxlive p n h) _ _
  let afterBlack : GlobalState := {xyState with alloc := (xyState.alloca 1).alloc}
  let states : FieldStates := ⟨powed, squared, inverted, xState, xyState⟩
  let words : FieldResults := ⟨first, second, squaredWords, inverse, affineX, affineY⟩
  refine ⟨states, afterBlack, words, ?_⟩
  refine ⟨?_, ?_, ?_, hilive _ _ hxslot, hxylive _ _ (halive _ _ hout),
    linked_blackBox_call _ xyState hxywf⟩
  · refine ⟨hinput, hpcall, hpair, hfirst, hsecond, ?_, ?_, hscall, hicall,
      hxcall, hxlive _ _ hinput, hxlive _ _ (hslot 5 (by decide)), hycall,
      hxylive _ _ (hslot 5 (by decide))⟩
    · exact Or.inl (hn 3 1 (by decide))
    · exact Or.inl (hn 2 1 (by decide))
  · refine ⟨hpmem, rfl, rfl, rfl, rfl, rfl, ?_⟩
    have hcounter : allocated.alloc.nextFreeBlock = initial.alloc.nextFreeBlock + 6 :=
      scratchState_counter initial 6
    change initial.alloc.nextFreeBlock ≤ powed.alloc.nextFreeBlock + 1
    omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [inputZ, hreadA _ hinputZ] using hpv1
    · simpa only [inputZ, hreadA _ hinputZ] using hpv2
    · simpa only [hcopyFirst] using hsv
    · simpa only [hsread, hssecond] using hiv
    · simpa only [inputX, hiold _ hinputX, hiread] using hxv
    · simpa only [inputY, hxyread, hxinv] using hyv

/-- The linked RIR compressor is total on a readable tight projective point.
The RIR execution also permits overlapping input and output: all three
coordinates are consumed before serialization. The verifier ABI retains the
source-level disjointness condition. -/
theorem linked_compress_call (out input : Pointer) (initial : GlobalState)
    (P : Bridge.CurvePoint) (hwf : initial.WF)
    (hout : SmallRange initial.mem out 32) (hin : SmallRange initial.mem input 160)
    (hx : SerialPoint.Tight (unsigned (readLimbs initial input)))
    (hy : SerialPoint.Tight (unsigned (readLimbs initial (input.add 40))))
    (hz : SerialPoint.Tight (unsigned (readLimbs initial (input.add 80))))
    (hrep : ProjectiveInput initial input P) :
    ∃ after,
      linkedProgram.call (Verifier.Execution.Dalek.args2 out input) initial =
        .value (.nil, after) ∧
      Verifier.Execution.Dalek.OutputFrame initial after out 32 ∧
      Verifier.Execution.Dalek.ReadBytes after out 32 (Bridge.compress P) := by
  obtain ⟨states, afterBlack, words, h⟩ :=
    linked_primitive_obligations out input initial hwf hout hin hx hy hz
  exact Verifier.Execution.Dalek.compress_call_of_primitive_obligations
    linkedPrimitives initial afterBlack input out states words h P hwf hout hrep

end Agave.Ed25519.Encoding.Compress.Execution

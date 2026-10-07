import SSA.Projects.Agave.Ed25519.Proof.Verifier.Bridge.ColdInputMemory

namespace Agave.Ed25519.Verifier.Execution.ColdInput
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

theorem afterKey_publicKey (initial decoded : GlobalState) (i : Invocation)
    (x t : Key.Words) (h : SmallRange decoded.mem (Wrapper.keyResultSlot initial) 200) :
    (WrapperKeyLink.afterKey initial decoded i x t true).mem.readAt
      ((Wrapper.keyResultSlot initial).add 8#64) 256 = decoded.mem.readAt i.publicKey 256 := by
  let out := Wrapper.keyResultSlot initial
  change SmallRange decoded.mem out 200 at h
  have hd (k w : Nat) (hk : 40 ≤ k) (hl : k ≤ 200) :
      (Range.of (out.add (BitVec.ofNat 64 k)) w).Disjoint (Range.of (out.add 8#64) 256) := by
    have ho := Pointer.offsetInBits_add (h.no_wrap (k := k) hl)
    have h8 := Pointer.offsetInBits_add (h.no_wrap (k := 8) (by decide))
    have hk64 : k < 2^64 := by omega
    simp only [Range.Disjoint, Range.of, ho, h8, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hk64, BitVec.toNat_ofNat]
    right; right; omega
  have htag : (Range.of out 8).Disjoint (Range.of (out.add 8#64) 256) := by
    have h8 := Pointer.offsetInBits_add (h.no_wrap (k := 8) (by decide))
    simp only [Range.Disjoint, Range.of, h8]
    right; left; norm_num
  unfold WrapperKeyLink.afterKey Key.returnedState
  dsimp only
  rw [Key.erase_read _ ((Wrapper.keyResultSlot initial).add 8#64) _ _ (result_lt initial)]
  simp only [Key.outputState, ↓reduceIte, Key.successState,
    Key.payloadState, Key.copyYZ]
  rw [MemoryState.readAt_storeAt_disjoint htag,
    MemoryState.readAt_storeAt_disjoint (hd 184 128 (by decide) (by decide)),
    MemoryState.readAt_storeAt_disjoint (hd 168 128 (by decide) (by decide)),
    MemoryState.readAt_storeAt_disjoint (hd 160 64 (by decide) (by decide)),
    MemoryState.readAt_storeAt_disjoint (hd 64 128 (by decide) (by decide)),
    MemoryState.readAt_storeAt_disjoint (hd 48 128 (by decide) (by decide)),
    MemoryState.readAt_storeAt_disjoint (hd 40 64 (by decide) (by decide))]
  exact MemoryState.readAt_storeAt_self
    (((h.storeAt _ _).storeAt _ _).fits_add (k := 8) (count := 32) (by decide)) _

theorem afterSignature_publicKey (initial decoded : GlobalState) (i : Invocation)
    (x t : Key.Words) (hresult : SmallRange decoded.mem (Wrapper.keyResultSlot initial) 200)
    (hkey : Fits decoded.mem (Wrapper.keySlot initial) 1536) :
    (LinkedLeaves.afterSignature i initial decoded x t true).mem.readAt
      (Wrapper.keySlot initial) 256 = decoded.mem.readAt i.publicKey 256 := by
  have hm := WrapperKeyLink.key_memory (i := i) (x := x) (t := t) (valid := true) hresult hkey
  have hsrc := Dalek.smallRange_add hm.resultRange (k := 8) (count := 192) (by decide)
  have hr := MemoryState.readAt_add_of_readAt (off := 0#64) (w := 256)
    hsrc.fits (hsrc.no_wrap (k := 0) (by decide)) (by decide)
    (rfl : (WrapperKeyLink.afterKey initial decoded i x t true).mem.readAt
      ((Wrapper.keyResultSlot initial).add 8#64) 1536 = _)
  simp only [Pointer.add_zero] at hr
  unfold LinkedLeaves.afterSignature
  rw [Signature.copied_read_frame]
  · unfold Wrapper.copiedKey
    have hs := MemoryState.readAt_storeAt_add (off := 0#64) (w := 256)
      hm.destinationFits (by simp [Wrapper.keySlot, GlobalState.allocaPtr, BitVec.uaddOverflow]) (by decide)
      ((WrapperKeyLink.afterKey initial decoded i x t true).mem.readAt
        ((Wrapper.keyResultSlot initial).add 8#64) 1536)
    simp only [Pointer.add_zero] at hs
    exact hs.trans (hr.symm.trans (afterKey_publicKey initial decoded i x t hresult))
  · simp [Wrapper.signatureSlot, Wrapper.keySlot, GlobalState.allocaPtr, GlobalState.alloca]
    omega

/-- Only concrete bytes and live ranges at the caller boundary. No fresh-stack
range or intermediate state is part of the caller's obligation. -/
structure CallerMemory (i : Invocation) (initial : GlobalState)
    (a r s : Bytes32) (message : List (BitVec 8)) : Prop where
  wellFormed : initial.WF
  publicKey : Dalek.ReadBytes initial i.publicKey 32 a
  signature : SmallRange initial.mem i.signature 64
  signatureR : initial.mem.readAt i.signature 256 = r
  signatureS : initial.mem.readAt (i.signature.add 32#64) 256 = s
  messageRange : SmallRange initial.mem i.message message.length
  messageBytes : ∀ (n : Nat) (hn : n < message.length),
    initial.mem.readAt (i.message.add (BitVec.ofNat 64 n)) 8 = message[n]
  length : i.length = BitVec.ofNat 64 message.length
  lengthBound : message.length < 2^63

theorem signatureMemory (dg : Dalek.Globals) (cg : Challenge.Globals)
    (layout : Dalek.Layout Point Scalar Result) (minusA : Point)
    (h : CallerMemory i initial a r s message)
    (hd : CallerBlocks (Wrapper.allocated initial) decoded) (hw : decoded.WF)
    (hi : Dalek.ReadBytes initial dg.address0 40 (1#320))
    (hc : SmallRange initial.mem dg.address1 1)
    (hv : Dalek.ReadBytes initial cg.address0 64 Challenge.initialWords) :
    LinkedConcretePayload.SignatureMemoryExceptPoint dg cg layout i initial decoded x t true
      a r s minusA message := by
  have hw0 := allocated_wf h.wellFormed
  have hkey := hd.range hw0 (allocated_key initial)
  have hsig := hd.range hw0 (allocated_signature h.wellFormed)
  have hresult := hd.range hw0 (allocated_result h.wellFormed)
  have hf := beforeSignature_blocks (i := i) (x := x) (t := t) (valid := true) h.wellFormed hd
  have hg := afterSignature_blocks (i := i) (x := x) (t := t) (valid := true) h.wellFormed hd
  have hsigBefore := beforeSignature_range (i := i) (x := x) (t := t) (valid := true)
    hsig (signature_lt initial)
  refine ⟨hkey.fits, beforeSignature_wf hw, hsigBefore,
    hf.range h.wellFormed h.signature,
    fresh_ne h.wellFormed h.signature (signature_fresh initial), ?_⟩
  refine ⟨afterSignature_wf hw, afterSignature_range hkey (key_lt initial),
    afterSignature_range hsig (signature_lt initial), hg.range h.wellFormed h.messageRange,
    ?_, ?_, ?_, ?_, h.lengthBound, hg.readBytes h.wellFormed hi,
    hg.range h.wellFormed hc, ?_, ?_, hg.readBytes h.wellFormed hv⟩
  · exact (afterSignature_publicKey initial decoded i x t hresult hkey.fits).trans
      ((hd.read hw0 ((allocated_blocks initial).range h.wellFormed h.publicKey.1) 256).trans
        (((allocated_blocks initial).read h.wellFormed h.publicKey.1 256).trans h.publicKey.2))
  · exact (Signature.copied_read_R _ _ _ hsigBefore).trans
      ((hf.read h.wellFormed h.signature 256).trans h.signatureR)
  · exact (Signature.copied_read_S _ _ _ hsigBefore).trans
      ((hf.read h.wellFormed (Dalek.smallRange_add h.signature (k := 32) (count := 32)
        (by decide)) 256).trans h.signatureS)
  · intro n hn
    exact (hg.read h.wellFormed (Dalek.smallRange_add h.messageRange (k := n) (count := 1)
      (by omega)) 8).trans (h.messageBytes n hn)
  · exact Range.disjoint_of_id_ne (fresh_ne h.wellFormed hc (key_fresh initial))
  · exact Range.disjoint_of_id_ne (fresh_ne h.wellFormed hc (signature_fresh initial))

end Agave.Ed25519.Verifier.Execution.ColdInput

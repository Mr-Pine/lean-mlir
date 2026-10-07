import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineCallsPrefix
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixMemory

/-! Reusable memory facts for composing the checked sqrt slices. This invariant
contains memory readiness only; no source execution or semantic output is a field. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
open SmallOrder.Execution (PrivateFrame)
set_option maxRecDepth 32000
set_option maxHeartbeats 2000000
attribute [local irreducible] ToBytes.storeBytes ToBytes.machine SerialFieldMul.machine

structure ScratchFrame (entry current : GlobalState) : Prop where
  publicFrame : PrivateFrame entry current
  slots : ∀ i : Fin 22, SmallRange current.mem (slot entry i) allocationSizes[i.val]

namespace ScratchFrame

theorem wf (h : ScratchFrame entry current) : current.WF := h.publicFrame.wellFormed

theorem old_live (h : ScratchFrame entry current) (hwf : entry.WF)
    {p : Pointer} (hp : SmallRange entry.mem p bytes) : SmallRange current.mem p bytes :=
  Decode.InlinePrefix.private_live h.publicFrame hwf hp

theorem old_read (h : ScratchFrame entry current) (hwf : entry.WF)
    {p : Pointer} (hp : SmallRange entry.mem p bytes) (bits : Nat) :
    current.mem.readAt p bits = entry.mem.readAt p bits :=
  Decode.InlinePrefix.private_read h.publicFrame p bits (hwf.lt hp.fits.mem)

theorem old_words (h : ScratchFrame entry current) (hwf : entry.WF)
    {p : Pointer} (hp : SmallRange entry.mem p bytes) :
    readLimbs current p = readLimbs entry p := by
  funext i
  exact Decode.InlinePrefix.private_read h.publicFrame (p.add _) 64 (hwf.lt hp.fits.mem)

theorem ready (h : ScratchFrame entry current) (hwf : entry.WF) (hr : Ready dg sg entry) :
    Ready dg sg current := Decode.InlinePrefix.private_ready h.publicFrame hwf hr

theorem advance (h : ScratchFrame entry current) (n : Nat) :
    ScratchFrame entry {current with alloc := ⟨current.alloc.nextFreeBlock+n⟩} :=
  ⟨h.publicFrame.advance n,h.slots⟩

theorem storeAt (h : ScratchFrame entry current) (p : Pointer) (x : BitVec bits)
    (hp : entry.alloc.nextFreeBlock ≤ p.id.id) :
    ScratchFrame entry {current with mem := current.mem.storeAt p x} :=
  ⟨h.publicFrame.storeAt p x hp,fun i => (h.slots i).storeAt p x⟩

theorem storeLimbs (h : ScratchFrame entry current) (p : Pointer) (x : Words)
    (hp : entry.alloc.nextFreeBlock ≤ p.id.id) :
    ScratchFrame entry {current with mem := SerialFieldMul.storeLimbs current.mem p x} :=
  ⟨h.publicFrame.storeLimbs p x hp,fun i => SerialPoint.Execution.smallRange_storeLimbs (h.slots i) p x⟩

theorem storeBytes (h : ScratchFrame entry current) (p : Pointer) (x : Fin 32 → BitVec 8)
    (hp : entry.alloc.nextFreeBlock ≤ p.id.id) :
    ScratchFrame entry {current with mem := ToBytes.storeBytes current.mem p x} :=
  ⟨h.publicFrame.storeBytes p x hp,fun i => ToBytes.smallRange_storeBytes (h.slots i) p x⟩

end ScratchFrame

theorem state117_scratch (s : GlobalState) (u v : Pointer) (hwf : s.WF) :
    ScratchFrame s (state117 s u v) := by
  have h := state117_private s u v hwf
  exact ⟨⟨state117_wf s u v hwf,by rw [h.2]; omega,h.1⟩,
    fun i => callsState_slot_live s _ _ hwf i 13⟩

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline

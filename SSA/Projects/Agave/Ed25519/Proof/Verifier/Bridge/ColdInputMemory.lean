import SSA.Projects.Agave.Ed25519.Proof.Verifier.LinkedColdLeaves

/-! Exact caller-memory transport through the constructor and both wrapper
copies. The public-key decoder's frame is a local, explicit premise. -/
namespace Agave.Ed25519.Verifier.Execution.ColdInput
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- Exact preservation of existing allocations. Unlike `OutputFrame`, this
also preserves allocation lengths and hence `ByteGlobal.Present`. -/
def CallerBlocks (before after : GlobalState) : Prop :=
  ∀ id : BlockId, id.id < before.alloc.nextFreeBlock →
    after.mem[id]? = before.mem[id]?

theorem CallerBlocks.range (h : CallerBlocks before after) (hwf : before.WF)
    (hr : SmallRange before.mem q n) : SmallRange after.mem q n := by
  obtain ⟨b, hb, hs, hn⟩ := hr
  exact ⟨b, (h q.id (hwf.lt (SmallRange.fits ⟨b, hb, hs, hn⟩).mem)).trans hb, hs, hn⟩

theorem CallerBlocks.read (h : CallerBlocks before after) (hwf : before.WF)
    (hr : SmallRange before.mem q n) (w : Nat) :
    after.mem.readAt q w = before.mem.readAt q w := by
  simp only [MemoryState.readAt, h q.id (hwf.lt hr.fits.mem)]

theorem CallerBlocks.readBytes (h : CallerBlocks before after) (hwf : before.WF)
    (hr : Dalek.ReadBytes before q n v) : Dalek.ReadBytes after q n v :=
  ⟨h.range hwf hr.1, (h.read hwf hr.1 _).trans hr.2⟩

theorem CallerBlocks.present {g : ByteGlobal} {id : BlockId} (h : CallerBlocks before after) (hwf : before.WF)
    (hp : g.Present id before.mem) : g.Present id after.mem := by
  have hf : Fits before.mem (g.address id) (8 * g.length) := hp.fits
  exact (h id (hwf.lt hf.mem)).trans hp

theorem alloca_blocks (s : GlobalState) (n : Nat) : CallerBlocks s (s.alloca n) := by
  intro id hi
  have hne : id ≠ s.allocaPtr.id := by
    intro heq
    have := congrArg BlockId.id heq
    simp only [GlobalState.allocaPtr] at this
    omega
  exact GlobalState.getElem?_alloca (q := id) hne

theorem allocated_blocks (s : GlobalState) : CallerBlocks s (Wrapper.allocated s) := by
  intro id hi
  unfold Wrapper.allocated
  rw [alloca_blocks _ _ id (by simp only [GlobalState.alloca]; omega),
    alloca_blocks _ _ id (by simp only [GlobalState.alloca]; omega),
    alloca_blocks _ _ id hi]

theorem allocated_wf (hwf : s.WF) : (Wrapper.allocated s).WF := hwf.alloca.alloca.alloca

theorem fresh_range (s : GlobalState) (n : Nat) (hn : n < 2^63) :
    SmallRange (s.alloca n).mem s.allocaPtr n := by
  refine ⟨⟨n, 0⟩, ?_, hn, ?_⟩
  · simp [GlobalState.alloca, GlobalState.allocaPtr, MemoryState.getElem?_eq]
  · simp [GlobalState.allocaPtr]

theorem allocated_signature (hwf : s.WF) :
    SmallRange (Wrapper.allocated s).mem (Wrapper.signatureSlot s) 64 :=
  Dalek.smallRange_alloca _ hwf.alloca.alloca
    (Dalek.smallRange_alloca _ hwf.alloca (fresh_range s 64 (by decide)) 200) 192

theorem allocated_result (hwf : s.WF) :
    SmallRange (Wrapper.allocated s).mem (Wrapper.keyResultSlot s) 200 :=
  Dalek.smallRange_alloca _ hwf.alloca.alloca (fresh_range (s.alloca 64) 200 (by decide)) 192

theorem allocated_key (s : GlobalState) :
    SmallRange (Wrapper.allocated s).mem (Wrapper.keySlot s) 192 :=
  fresh_range ((s.alloca 64).alloca 200) 192 (by decide)

theorem key_lt (s : GlobalState) :
    (Wrapper.keySlot s).id.id < (Wrapper.allocated s).alloc.nextFreeBlock := by
  simp [Wrapper.keySlot, Wrapper.allocated, GlobalState.alloca, GlobalState.allocaPtr]

theorem signature_lt (s : GlobalState) :
    (Wrapper.signatureSlot s).id.id < (Wrapper.allocated s).alloc.nextFreeBlock := by
  simp [Wrapper.signatureSlot, Wrapper.allocated, GlobalState.alloca, GlobalState.allocaPtr]
  omega

theorem result_lt (s : GlobalState) :
    (Wrapper.keyResultSlot s).id.id < (Wrapper.allocated s).alloc.nextFreeBlock := by
  simp [Wrapper.keyResultSlot, Wrapper.allocated, GlobalState.alloca, GlobalState.allocaPtr]

theorem fresh_ne {s : GlobalState} {p : Pointer} (hwf : s.WF) (hr : SmallRange s.mem q n)
    (hp : s.alloc.nextFreeBlock ≤ p.id.id) : p.id ≠ q.id := by
  have hq := hwf.lt hr.fits.mem
  intro heq
  have := congrArg BlockId.id heq
  omega

theorem signature_fresh (s : GlobalState) :
    s.alloc.nextFreeBlock ≤ (Wrapper.signatureSlot s).id.id := by
  simp [Wrapper.signatureSlot, GlobalState.allocaPtr]

theorem key_fresh (s : GlobalState) : s.alloc.nextFreeBlock ≤ (Wrapper.keySlot s).id.id := by
  simp [Wrapper.keySlot, GlobalState.allocaPtr, GlobalState.alloca]
  omega

theorem result_fresh (s : GlobalState) :
    s.alloc.nextFreeBlock ≤ (Wrapper.keyResultSlot s).id.id := by
  simp [Wrapper.keyResultSlot, GlobalState.allocaPtr, GlobalState.alloca]

theorem output_range (hr : SmallRange s.mem q n) :
    SmallRange (Key.outputState s out opt bytes x t valid).mem q n := by
  cases valid <;> simp [Key.outputState, Key.rejectedState, Key.successState,
    Key.payloadState, Key.copyYZ] <;> repeat' apply SmallRange.storeAt
  all_goals exact hr

theorem output_wf (hwf : s.WF) : (Key.outputState s out opt bytes x t valid).WF := by
  cases valid <;> simpa [Key.outputState, Key.rejectedState, Key.successState,
    Key.payloadState, Key.copyYZ, GlobalState.WF_storeAt] using hwf

theorem output_get (s : GlobalState) (out opt bytes q : Pointer) (x t : Key.Words)
    (valid : Bool) (hne : q.id ≠ out.id) :
    (Key.outputState s out opt bytes x t valid).mem[q.id]? = s.mem[q.id]? := by
  have ha (k : BitVec 64) : q.id ≠ (out.add k).id := hne
  cases valid <;> simp [Key.outputState, Key.rejectedState, Key.successState,
    Key.payloadState, Key.copyYZ, MemoryState.getElem?_storeAt_ne hne,
    MemoryState.getElem?_storeAt_ne (ha _)]

theorem erase_wf {s : GlobalState} (hwf : s.WF) (mark : Nat) :
    ({s with mem := s.mem.eraseFrom mark} : GlobalState).WF := by
  intro id hi
  exact hwf id (Std.ExtHashMap.mem_filter.mp hi).1

theorem afterKey_wf (hwf : decoded.WF) :
    (WrapperKeyLink.afterKey initial decoded i x t valid).WF :=
  erase_wf (output_wf hwf) _

theorem afterKey_range (hr : SmallRange decoded.mem q n)
    (hq : q.id.id < (Wrapper.allocated initial).alloc.nextFreeBlock) :
    SmallRange (WrapperKeyLink.afterKey initial decoded i x t valid).mem q n :=
  Key.erase_range (output_range hr) hq

theorem afterKey_get (initial decoded : GlobalState) (i : Invocation) (x t : Key.Words)
    (valid : Bool) (q : Pointer)
    (hne : q.id ≠ (Wrapper.keyResultSlot initial).id)
    (hq : q.id.id < (Wrapper.allocated initial).alloc.nextFreeBlock) :
    (WrapperKeyLink.afterKey initial decoded i x t valid).mem[q.id]? = decoded.mem[q.id]? := by
  unfold WrapperKeyLink.afterKey Key.returnedState
  rw [Key.erase_get _ _ _ hq, output_get _ _ _ _ q _ _ _ hne]

theorem beforeSignature_wf (hwf : decoded.WF) :
    (Wrapper.copiedKey initial (WrapperKeyLink.afterKey initial decoded i x t valid)).WF :=
  (afterKey_wf hwf).storeAt

theorem beforeSignature_range (hr : SmallRange decoded.mem q n)
    (hq : q.id.id < (Wrapper.allocated initial).alloc.nextFreeBlock) :
    SmallRange (Wrapper.copiedKey initial
      (WrapperKeyLink.afterKey initial decoded i x t valid)).mem q n :=
  (afterKey_range hr hq).storeAt _ _

theorem afterSignature_range (hr : SmallRange decoded.mem q n)
    (hq : q.id.id < (Wrapper.allocated initial).alloc.nextFreeBlock) :
    SmallRange (LinkedLeaves.afterSignature i initial decoded x t valid).mem q n :=
  Signature.copied_smallRange _ _ _ _ _ (beforeSignature_range hr hq)

theorem afterSignature_wf (hwf : decoded.WF) :
    (LinkedLeaves.afterSignature i initial decoded x t valid).WF :=
  Signature.copied_wf _ _ _ (beforeSignature_wf hwf)

theorem beforeSignature_blocks (_hwf : initial.WF)
    (hd : CallerBlocks (Wrapper.allocated initial) decoded) :
    CallerBlocks initial
      (Wrapper.copiedKey initial (WrapperKeyLink.afterKey initial decoded i x t valid)) := by
  intro id hi
  have hl : id.id < (Wrapper.allocated initial).alloc.nextFreeBlock := by
    simp only [Wrapper.allocated, GlobalState.alloca] at *
    omega
  have hk : id ≠ (Wrapper.keySlot initial).id := by
    intro heq; have := congrArg BlockId.id heq; have := key_fresh initial; omega
  have hr : id ≠ (Wrapper.keyResultSlot initial).id := by
    intro heq; have := congrArg BlockId.id heq; have := result_fresh initial; omega
  dsimp only [Wrapper.copiedKey]
  rw [MemoryState.getElem?_storeAt_ne (q := ⟨id, 0⟩) hk,
    afterKey_get initial decoded i x t valid ⟨id, 0⟩ hr hl, hd id hl,
    allocated_blocks initial id hi]

theorem afterSignature_blocks (hwf : initial.WF)
    (hd : CallerBlocks (Wrapper.allocated initial) decoded) :
    CallerBlocks initial (LinkedLeaves.afterSignature i initial decoded x t valid) := by
  intro id hi
  have hs : id ≠ (Wrapper.signatureSlot initial).id := by
    intro heq; have := congrArg BlockId.id heq; have := signature_fresh initial; omega
  unfold LinkedLeaves.afterSignature Signature.copied
  dsimp only
  rw [MemoryState.getElem?_storeAt_ne (q := ⟨id, 0⟩) (p := (Wrapper.signatureSlot initial).add 32#64) hs,
    MemoryState.getElem?_storeAt_ne (q := ⟨id, 0⟩) hs,
    beforeSignature_blocks hwf hd id hi]

end Agave.Ed25519.Verifier.Execution.ColdInput

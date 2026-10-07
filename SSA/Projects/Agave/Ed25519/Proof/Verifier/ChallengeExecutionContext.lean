import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionMemory

namespace Agave.Ed25519.Verifier.Execution.Challenge

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge

/-- The fields that remain meaningful while the 128-byte buffer is full.
The full buffer temporarily overwrites the partial-length byte at offset 127. -/
structure ChainRepresents (sha : Sha512Model) (m : MemoryState) (ctx : Pointer)
    (completed : Bytes) : Prop where
  live : SmallRange m ctx 208
  whole : completed.length % 128 = 0
  chaining : m.readAt (ctx.add 128) 512 = sha.compress initialWords completed
  blockCount : (m.readAt (ctx.add 192) 128).toNat = completed.length / 128

theorem ContextRepresents.chain (h : ContextRepresents sha m ctx completed pending) :
    ChainRepresents sha m ctx completed :=
  ⟨h.live, h.completedWhole, h.chaining, h.blockCount⟩

def initContext (m : MemoryState) (ctx : Pointer) : MemoryState :=
  ((m.storeAt (ctx.add 127) (64#8)).storeAt (ctx.add 128) initialWords).storeAt
    (ctx.add 192) (0#128)

theorem init_context (sha : Sha512Model) (m : MemoryState) (ctx : Pointer)
    (pending : Bytes) (hlive : SmallRange m ctx 208)
    (hlen : pending.length = 64) (hbytes : readBytes m ctx 64 = pending) :
    ContextRepresents sha (initContext m ctx) ctx [] pending := by
  have hd192128 : (Range.of (ctx.add 192) 128).Disjoint (Range.of (ctx.add 128) 512) := smallRange_disjoint_offsets hlive
    (i := 192) (countI := 16) (j := 128) (countJ := 64) (by decide) (by decide)
    (Or.inr (by decide))
  have hd192127 : (Range.of (ctx.add 192) 128).Disjoint (Range.of (ctx.add 127) 8) := smallRange_disjoint_offsets hlive
    (i := 192) (countI := 16) (j := 127) (countJ := 1) (by decide) (by decide)
    (Or.inr (by decide))
  have hd128127 : (Range.of (ctx.add 128) 512).Disjoint (Range.of (ctx.add 127) 8) := smallRange_disjoint_offsets hlive
    (i := 128) (countI := 64) (j := 127) (countJ := 1) (by decide) (by decide)
    (Or.inr (by decide))
  have hp127 : (Range.of (ctx.add 127) 8).Disjoint (Range.of ctx 512) := by
    simpa using smallRange_disjoint_offsets hlive
      (i := 127) (countI := 1) (j := 0) (countJ := 64) (by decide) (by decide)
      (Or.inr (by decide))
  have hp128 : (Range.of (ctx.add 128) 512).Disjoint (Range.of ctx 512) := by
    simpa using smallRange_disjoint_offsets hlive
      (i := 128) (countI := 64) (j := 0) (countJ := 64) (by decide) (by decide)
      (Or.inr (by decide))
  have hp192 : (Range.of (ctx.add 192) 128).Disjoint (Range.of ctx 512) := by
    simpa using smallRange_disjoint_offsets hlive
      (i := 192) (countI := 16) (j := 0) (countJ := 64) (by decide) (by decide)
      (Or.inr (by decide))
  refine ⟨((hlive.storeAt _ _).storeAt _ _).storeAt _ _, by simp, by omega, ?_, ?_, ?_, ?_⟩
  · rw [hlen]
    unfold initContext
    rw [readBytes_storeAt_disjoint _ _ _ _ _
        (smallRange_mono ((hlive.storeAt _ _).storeAt _ _) (by decide)) hp192,
      readBytes_storeAt_disjoint _ _ _ _ _
        (smallRange_mono (hlive.storeAt _ _) (by decide)) hp128,
      readBytes_storeAt_disjoint _ _ _ _ _ (smallRange_mono hlive (by decide)) hp127]
    exact hbytes
  · unfold initContext
    rw [MemoryState.readAt_storeAt_disjoint hd192127,
      MemoryState.readAt_storeAt_disjoint hd128127,
      MemoryState.readAt_storeAt_self (context_count_fits hlive)]
    exact hlen.symm
  · unfold initContext
    rw [MemoryState.readAt_storeAt_disjoint hd192128,
      MemoryState.readAt_storeAt_self
        (context_chain_fits (hlive.storeAt _ _)), sha.empty]
  · unfold initContext
    rw [MemoryState.readAt_storeAt_self
      (context_blocks_fits ((hlive.storeAt _ _).storeAt _ _))]
    rfl

def appendPending (m : MemoryState) (ctx src : Pointer) (old count : Nat) : MemoryState :=
  (m.storeAt (ctx.add (BitVec.ofNat 64 old)) (m.readAt src (8 * count))).storeAt
    (ctx.add 127) (BitVec.ofNat 8 (old + count))

theorem append_pending (sha : Sha512Model) (m : MemoryState) (ctx src : Pointer)
    (completed pending more : Bytes)
    (hctx : ContextRepresents sha m ctx completed pending)
    (hsrc : SmallRange m src more.length) (hmore : readBytes m src more.length = more)
    (hbound : pending.length + more.length < 128) :
    ContextRepresents sha (appendPending m ctx src pending.length more.length)
      ctx completed (pending ++ more) := by
  have hbuf := smallRange_mono hctx.live (k := pending.length + more.length) (by omega)
  have hd127buf : (Range.of (ctx.add 127) 8).Disjoint
      (Range.of ctx (8 * (pending.length + more.length))) := by
    simpa using smallRange_disjoint_offsets hctx.live
      (i := 127) (countI := 1) (j := 0) (countJ := pending.length + more.length)
      (by decide) (by omega) (Or.inr (by omega))
  have hd127128 : (Range.of (ctx.add 127) 8).Disjoint (Range.of (ctx.add 128) 512) := smallRange_disjoint_offsets hctx.live
    (i := 127) (countI := 1) (j := 128) (countJ := 64) (by decide) (by decide)
    (Or.inl (by decide))
  have hd127192 : (Range.of (ctx.add 127) 8).Disjoint (Range.of (ctx.add 192) 128) := smallRange_disjoint_offsets hctx.live
    (i := 127) (countI := 1) (j := 192) (countJ := 16) (by decide) (by decide)
    (Or.inl (by decide))
  have hdbuf128 : (Range.of (ctx.add (BitVec.ofNat 64 pending.length)) (8 * more.length)).Disjoint (Range.of (ctx.add 128) 512) := smallRange_disjoint_offsets hctx.live
    (i := pending.length) (countI := more.length) (j := 128) (countJ := 64)
    (by omega) (by decide) (Or.inl (by omega))
  have hdbuf192 : (Range.of (ctx.add (BitVec.ofNat 64 pending.length)) (8 * more.length)).Disjoint (Range.of (ctx.add 192) 128) := smallRange_disjoint_offsets hctx.live
    (i := pending.length) (countI := more.length) (j := 192) (countJ := 16)
    (by omega) (by decide) (Or.inl (by omega))
  refine ⟨(hctx.live.storeAt _ _).storeAt _ _, hctx.completedWhole, by simpa, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append]
    unfold appendPending
    rw [readBytes_storeAt_disjoint _ _ _ _ _ (hbuf.storeAt _ _) hd127buf,
      readBytes_copy_append _ _ _ _ _ hsrc hbuf, hctx.pendingBytes, hmore]
  · unfold appendPending
    rw [MemoryState.readAt_storeAt_self
      (context_count_fits (hctx.live.storeAt _ _))]
    simp only [BitVec.toNat_ofNat, List.length_append]
    apply Nat.mod_eq_of_lt
    omega
  · unfold appendPending
    rw [MemoryState.readAt_storeAt_disjoint hd127128,
      MemoryState.readAt_storeAt_disjoint hdbuf128]
    exact hctx.chaining
  · unfold appendPending
    rw [MemoryState.readAt_storeAt_disjoint hd127192,
      MemoryState.readAt_storeAt_disjoint hdbuf192]
    exact hctx.blockCount

def finishContext (m : MemoryState) (ctx src : Pointer) (count : Nat) : MemoryState :=
  let m' := m.storeAt (ctx.add 127) (BitVec.ofNat 8 count)
  m'.storeAt ctx (m'.readAt src (8 * count))

theorem finish_context (sha : Sha512Model) (m : MemoryState) (ctx src : Pointer)
    (completed pending : Bytes) (hc : ChainRepresents sha m ctx completed)
    (hsrc : SmallRange m src pending.length)
    (hbytes : readBytes m src pending.length = pending)
    (hbound : pending.length < 128) (hne : ctx.id ≠ src.id) :
    ContextRepresents sha (finishContext m ctx src pending.length) ctx completed pending := by
  have hd127src : (Range.of (ctx.add 127) 8).Disjoint
      (Range.of src (8 * pending.length)) := Or.inl hne
  have hdbuf127 : (Range.of ctx (8 * pending.length)).Disjoint
      (Range.of (ctx.add 127) 8) := by
    simpa using smallRange_disjoint_offsets hc.live
      (i := 0) (countI := pending.length) (j := 127) (countJ := 1)
      (by omega) (by decide) (Or.inl (by omega))
  have hdbuf128 : (Range.of ctx (8 * pending.length)).Disjoint
      (Range.of (ctx.add 128) 512) := by
    simpa using smallRange_disjoint_offsets hc.live
      (i := 0) (countI := pending.length) (j := 128) (countJ := 64)
      (by omega) (by decide) (Or.inl (by omega))
  have hdbuf192 : (Range.of ctx (8 * pending.length)).Disjoint
      (Range.of (ctx.add 192) 128) := by
    simpa using smallRange_disjoint_offsets hc.live
      (i := 0) (countI := pending.length) (j := 192) (countJ := 16)
      (by omega) (by decide) (Or.inl (by omega))
  have hd127128 : (Range.of (ctx.add 127) 8).Disjoint (Range.of (ctx.add 128) 512) := smallRange_disjoint_offsets hc.live
    (i := 127) (countI := 1) (j := 128) (countJ := 64) (by decide) (by decide)
    (Or.inl (by decide))
  have hd127192 : (Range.of (ctx.add 127) 8).Disjoint (Range.of (ctx.add 192) 128) := smallRange_disjoint_offsets hc.live
    (i := 127) (countI := 1) (j := 192) (countJ := 16) (by decide) (by decide)
    (Or.inl (by decide))
  refine ⟨(hc.live.storeAt _ _).storeAt _ _, hc.whole, hbound, ?_, ?_, ?_, ?_⟩
  · unfold finishContext
    rw [readBytes_copy _ _ _ _ (hsrc.storeAt _ _)
        (smallRange_mono (hc.live.storeAt _ _) (by omega)),
      readBytes_storeAt_disjoint _ _ _ _ _ hsrc hd127src]
    exact hbytes
  · unfold finishContext
    rw [MemoryState.readAt_storeAt_disjoint hdbuf127,
      MemoryState.readAt_storeAt_self (context_count_fits hc.live)]
    exact Nat.mod_eq_of_lt (by omega)
  · unfold finishContext
    rw [MemoryState.readAt_storeAt_disjoint hdbuf128,
      MemoryState.readAt_storeAt_disjoint hd127128]
    exact hc.chaining
  · unfold finishContext
    rw [MemoryState.readAt_storeAt_disjoint hdbuf192,
      MemoryState.readAt_storeAt_disjoint hd127192]
    exact hc.blockCount

/-- Buffer writes do not alter either chaining words or the full-block count,
including the special 128-byte first-block write. -/
theorem ChainRepresents.buffer_store (hc : ChainRepresents sha m ctx completed)
    (offset count : Nat) (hbound : offset + count ≤ 128) (value : BitVec (8 * count)) :
    ChainRepresents sha (m.storeAt (ctx.add (BitVec.ofNat 64 offset)) value) ctx completed := by
  have hd128 : (Range.of (ctx.add (BitVec.ofNat 64 offset)) (8 * count)).Disjoint
      (Range.of (ctx.add 128) 512) :=
    smallRange_disjoint_offsets hc.live (i := offset) (countI := count)
      (j := 128) (countJ := 64) (by omega) (by decide) (Or.inl hbound)
  have hd192 : (Range.of (ctx.add (BitVec.ofNat 64 offset)) (8 * count)).Disjoint
      (Range.of (ctx.add 192) 128) :=
    smallRange_disjoint_offsets hc.live (i := offset) (countI := count)
      (j := 192) (countJ := 16) (by omega) (by decide) (Or.inl (by omega))
  refine ⟨hc.live.storeAt _ _, hc.whole, ?_, ?_⟩
  · rw [MemoryState.readAt_storeAt_disjoint hd128]
    exact hc.chaining
  · rw [MemoryState.readAt_storeAt_disjoint hd192]
    exact hc.blockCount

def advanceCount (s : GlobalState) (ctx : Pointer) (q : BitVec 64) : GlobalState :=
  {s with mem :=
    s.mem.storeAt (ctx.add 192) (s.mem.readAt (ctx.add 192) 128 + q.setWidth 128)}

/-- A local compression-call contract suffices to update the exact two
full-block fields. The counter update is executed by the caller; the primitive
only updates the chaining words. -/
theorem compress_blocks (compressCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (sha : Sha512Model) (hcompress : CompressContract compressCall sha)
    (s : GlobalState) (ctx src : Pointer) (q : BitVec 64) (completed blocks : Bytes)
    (hwf : s.WF) (hc : ChainRepresents sha s.mem ctx completed)
    (hsrc : SmallRange s.mem src (128 * q.toNat))
    (hbytes : readBytes s.mem src (128 * q.toNat) = blocks)
    (hlen : blocks.length = 128 * q.toNat)
    (hchain : (Range.of (ctx.add 128) 512).Disjoint
      (Range.of src (8 * (128 * q.toNat))))
    (hcounter : (Range.of (ctx.add 192) 128).Disjoint
      (Range.of src (8 * (128 * q.toNat))))
    (hq : 0 < q.toNat) (hqbound : q.toNat < 2 ^ 56)
    (hcount : completed.length / 128 + q.toNat < 2 ^ 128) :
    ∃ after,
      compressCall (.cons (.value (ctx.add 128)) (.cons (.value src)
        (.cons (.value q) .nil))) (advanceCount s ctx q) = .value (.nil, after) ∧
      StoreEffect (advanceCount s ctx q) after (ctx.add 128)
        (sha.compress (sha.compress initialWords completed) blocks) ∧
      ChainRepresents sha after.mem ctx (completed ++ blocks) ∧ after.WF := by
  let counted := advanceCount s ctx q
  have hcounted : counted.WF := GlobalState.WF.storeAt hwf
  have hlive : SmallRange counted.mem ctx 208 := hc.live.storeAt _ _
  have hs : SmallRange counted.mem src (128 * q.toNat) := hsrc.storeAt _ _
  have hdc : (Range.of (ctx.add 192) 128).Disjoint (Range.of (ctx.add 128) 512) :=
    smallRange_disjoint_offsets hc.live (i := 192) (countI := 16)
      (j := 128) (countJ := 64) (by decide) (by decide) (Or.inr (by decide))
  have hrchain : counted.mem.readAt (ctx.add 128) 512 = sha.compress initialWords completed := by
    dsimp only [counted, advanceCount]
    rw [MemoryState.readAt_storeAt_disjoint hdc]
    exact hc.chaining
  have hrdata : readBytes counted.mem src (128 * q.toNat) = blocks := by
    dsimp only [counted, advanceCount]
    rw [readBytes_storeAt_disjoint _ _ _ _ _ hsrc hcounter]
    exact hbytes
  obtain ⟨after, hcall, heffect⟩ := hcompress counted (ctx.add 128) src q hcounted
    (smallRange_add hlive (k := 128) (count := 64) (by decide)) hs hchain hq hqbound
  rw [hrchain, hrdata] at heffect
  refine ⟨after, hcall, heffect, ?_, heffect.wellFormed hcounted⟩
  have hwhole : blocks.length % 128 = 0 := by rw [hlen]; omega
  have hprior := hc.whole
  refine ⟨heffect.smallRange hlive, ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · rw [heffect.memory, MemoryState.readAt_storeAt_self (context_chain_fits hlive),
      sha.append _ _ _ hc.whole hwhole]
  · rw [heffect.memory, MemoryState.readAt_storeAt_disjoint hdc.symm]
    dsimp only [counted, advanceCount]
    rw [MemoryState.readAt_storeAt_self (context_blocks_fits hc.live), BitVec.toNat_add,
      BitVec.toNat_setWidth, hc.blockCount]
    have hq128 : q.toNat < 2 ^ 128 := by omega
    rw [Nat.mod_eq_of_lt hq128, Nat.mod_eq_of_lt hcount]
    simp only [List.length_append, hlen]
    omega

end Agave.Ed25519.Verifier.Execution.Challenge

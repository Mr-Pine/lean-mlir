import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionBlocks
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionFinal

namespace Agave.Ed25519.Verifier.Execution.Challenge

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge

variable {s t : GlobalState} {dst copy ptr : Pointer} {w : Nat} {x : BitVec w}
variable {p : Primitives} {g : Globals} {sha : Sha512Model}

structure FinalRegisters (E : Env program.Γ) (dst ctx copy : Pointer) : Prop where
  output : E.read (%arg0) = .value dst
  context : E.read (%18) = .value ctx
  scratch : E.read (%19) = .value copy
  bytes : E.read (%16) = .value 208#64

structure OutputResources (s : GlobalState) (dst copy : Pointer) : Prop where
  output : SmallRange s.mem dst 32
  copy : SmallRange s.mem copy 208

theorem OutputResources.store (h : OutputResources s dst copy) (p : Pointer) (x : BitVec w) :
    OutputResources {s with mem := s.mem.storeAt p x} dst copy :=
  ⟨h.output.storeAt _ _, h.copy.storeAt _ _⟩

theorem OutputResources.effect (h : OutputResources s dst copy) (he : StoreEffect s t ptr x) :
    OutputResources t dst copy := ⟨he.smallRange h.output, he.smallRange h.copy⟩

/-- Successful actual execution and the exact caller-visible memory effect
after erasing this function's frame. -/
def Finalizes (p : Primitives) (g : Globals) (sha : Sha512Model)
    (E : Env program.Γ) (block : Fin 8) (s : GlobalState) (dst : Pointer)
    (input : Bytes) (mark : Nat) (base : MemoryState) : Prop :=
  ∃ after, (program p g).runFrom E block s = .value (.nil, after) ∧
    after.mem.eraseFrom mark = base.storeAt dst (digestScalarBytes (sha.digest input)) ∧ after.WF

/-- The exact prefix boundary: the actual run reaches bb7 with a valid
incremental context for precisely `input`, before invoking the scalar callee. -/
def ReachesFinal (p : Primitives) (g : Globals) (sha : Sha512Model)
    (E : Env program.Γ) (block : Fin 8) (s : GlobalState) (dst ctx copy : Pointer)
    (input : Bytes) (mark : Nat) (base : MemoryState) : Prop :=
  ∃ F t completed pending,
    (program p g).runFrom E block s = (program p g).runFrom F 7 t ∧
    FinalRegisters F dst ctx copy ∧ ContextRepresents sha t.mem ctx completed pending ∧
    input = completed ++ pending ∧ OutputResources t dst copy ∧ t.WF ∧
    t.mem.eraseFrom mark = base

theorem ReachesFinal.prepend
    (h : ReachesFinal p g sha F next t dst ctx copy input mark base)
    (heq : (program p g).runFrom E block s = (program p g).runFrom F next t) :
    ReachesFinal p g sha E block s dst ctx copy input mark base := by
  rcases h with ⟨F', t', completed, pending, hrun, hr, hc, hb, ho, hw, hf⟩
  exact ⟨F', t', completed, pending, heq.trans hrun, hr, hc, hb, ho, hw, hf⟩

theorem final_block_framed (p : Primitives) (g : Globals) (sha : Sha512Model)
    (hscalar : ScalarFromSha512Contract p.scalarFromSha512 sha)
    (E : Env program.Γ) (s : GlobalState) (dst ctx copy : Pointer)
    (completed pending : Bytes) (mark : Nat) (base : MemoryState)
    (hr : FinalRegisters E dst ctx copy) (hwf : s.WF)
    (hout : OutputResources s dst copy)
    (hc : ContextRepresents sha s.mem ctx completed pending)
    (hcc : copy.id ≠ ctx.id) (hoc : dst.id ≠ copy.id)
    (hcopy : mark ≤ copy.id.id) (hframe : s.mem.eraseFrom mark = base) :
    Finalizes p g sha E 7 s dst (completed ++ pending) mark base := by
  let copied : GlobalState := {s with mem := s.mem.storeAt copy (s.mem.readAt ctx 1664)}
  have hctx : ContextRepresents sha copied.mem copy completed pending :=
    ContextRepresents.copy sha s.mem ctx copy completed pending hc hout.copy
  obtain ⟨after, hcall, he⟩ := hscalar copied dst copy completed pending hwf.storeAt
    (hout.output.storeAt _ _) hctx (Or.inl hoc)
  refine ⟨after, ?_, ?_, he.wellFormed hwf.storeAt⟩
  · exact final_block p g E s after dst ctx copy hr.output hr.context hr.scratch hr.bytes
      hc.live.fits hout.copy.fits (Or.inl hcc) hcall
  · rw [he.memory, MemoryState.eraseFrom_storeAt]
    dsimp only [copied]
    rw [erase_internal_store s.mem base mark copy (s.mem.readAt ctx 1664) hframe hcopy]

theorem ReachesFinal.finalizes (p : Primitives) (g : Globals) (sha : Sha512Model)
    (hscalar : ScalarFromSha512Contract p.scalarFromSha512 sha)
    (h : ReachesFinal p g sha E block s dst ctx copy input mark base)
    (hcc : copy.id ≠ ctx.id) (hoc : dst.id ≠ copy.id) (hcopy : mark ≤ copy.id.id) :
    Finalizes p g sha E block s dst input mark base := by
  rcases h with ⟨F, t, completed, pending, hrun, hr, hc, hb, ho, hw, hf⟩
  obtain ⟨after, hdone, hm, hw'⟩ := final_block_framed p g sha hscalar F t dst ctx copy
    completed pending mark base hr hw ho hc hcc hoc hcopy hf
  exact ⟨after, hrun.trans hdone, by simpa only [hb] using hm, hw'⟩

theorem tail_reaches_final (p : Primitives) (g : Globals) (sha : Sha512Model)
    (E : Env program.Γ) (s : GlobalState) (dst ctx copy src : Pointer)
    (n : BitVec 64) (completed pending : Bytes) (mark : Nat) (base : MemoryState)
    (hr : FinalRegisters E dst ctx copy)
    (hsrc : E.read (%40) = .value src) (hn : E.read (%39) = .value n)
    (hptr : E.read (%25) = .value (ctx.add 127#64))
    (hwf : s.WF) (hout : OutputResources s dst copy)
    (hc : ChainRepresents sha s.mem ctx completed)
    (hinput : SmallRange s.mem src n.toNat)
    (hread : readBytes s.mem src n.toNat = pending) (hsmall : n.toNat < 128)
    (hne : ctx.id ≠ src.id) (hcc : copy.id ≠ ctx.id) (hoc : dst.id ≠ copy.id)
    (hctx : mark ≤ ctx.id.id) (hcopy : mark ≤ copy.id.id)
    (hframe : s.mem.eraseFrom mark = base) :
    ReachesFinal p g sha E 6 s dst ctx copy (completed ++ pending) mark base := by
  have hlen : pending.length = n.toNat := by rw [← hread, readBytes_length]
  have hcontext : ContextRepresents sha (tailState s ctx src n).mem ctx completed pending := by
    dsimp only [tailState]
    rw [← hlen]
    exact finish_context sha s.mem ctx src completed pending hc
      (by simpa [hlen] using hinput) (by simpa [hlen] using hread) (by omega) hne
  have hr' : FinalRegisters (tailEnv E n) dst ctx copy := by
    rcases hr with ⟨h0, h18, h19, h16⟩
    constructor <;> simp_all [tailEnv, mlir_env]
  have hframe' : (tailState s ctx src n).mem.eraseFrom mark = base :=
    erase_internal_store _ _ _ _ _ (erase_internal_store _ _ _ _ _ hframe hctx) hctx
  exact ⟨tailEnv E n, tailState s ctx src n, completed, pending,
    tail_block p g E s ctx src n hr.context hsrc hn hptr hc.live hinput hsmall hne,
    hr', hcontext, rfl, (hout.store _ _).store _ _, hwf.storeAt.storeAt, hframe'⟩

structure RemainingRegisters (E : Env program.Γ) (dst ctx copy src : Pointer)
    (n : BitVec 64) : Prop extends FinalRegisters E dst ctx copy where
  source : E.read (%36) = .value src
  length : E.read (%35) = .value n
  chain : E.read (%24) = .value (ctx.add 128#64)
  count : E.read (%25) = .value (ctx.add 127#64)
  shift : E.read (%13) = .value 7#64
  mask : E.read (%14) = .value 9223372036854775680#64
  remMask : E.read (%2) = .value 127#64
  counter : E.read (%7) = .value 192#64
  zero : E.read (%15) = .value 0#64

/-- All remaining complete blocks are passed directly from the message;
the residual is copied back to the context before finalization. -/
theorem remaining_reaches_final (p : Primitives) (g : Globals) (sha : Sha512Model)
    (hcompress : CompressContract p.sha512Compress sha)
    (E : Env program.Γ) (s : GlobalState) (dst ctx copy src : Pointer)
    (n : BitVec 64) (completed remaining : Bytes) (mark : Nat) (base : MemoryState)
    (hr : RemainingRegisters E dst ctx copy src n) (hwf : s.WF)
    (hout : OutputResources s dst copy) (hc : ChainRepresents sha s.mem ctx completed)
    (hinput : SmallRange s.mem src n.toNat)
    (hread : readBytes s.mem src n.toNat = remaining)
    (hcount : completed.length / 128 + n.toNat / 128 < 2 ^ 128)
    (hne : ctx.id ≠ src.id) (hcc : copy.id ≠ ctx.id) (hoc : dst.id ≠ copy.id)
    (hctx : mark ≤ ctx.id.id) (hcopy : mark ≤ copy.id.id)
    (hframe : s.mem.eraseFrom mark = base) :
    ReachesFinal p g sha E 3 s dst ctx copy (completed ++ remaining) mark base := by
  let q := n >>> 7
  let off := n &&& 9223372036854775680#64
  let rem := n &&& 127#64
  let tail := src.add off
  have hq : q.toNat = n.toNat / 128 := full_block_count n
  have ho : off.toNat = 128 * (n.toNat / 128) := full_block_offset n (smallRange_length_lt hinput)
  have ht : rem.toNat = n.toNat % 128 := remaining_byte_count n
  have hrem : rem.toNat < 128 := by omega
  have hlen : remaining.length = n.toNat := by rw [← hread, readBytes_length]
  have hoff : off.toNat ≤ n.toNat := by omega
  have htail : SmallRange s.mem tail rem.toNat := by
    have h := smallRange_add hinput (k := off.toNat) (count := rem.toNat) (by omega)
    simpa [tail] using h
  have htailRead : readBytes s.mem tail rem.toNat = remaining.drop off.toNat := by
    rw [← hread, readBytes_drop _ _ _ _ hoff]
    have heq : n.toNat - off.toNat = rem.toNat := by omega
    simpa [heq, tail]
  have hsplit : (remaining.take off.toNat ++ remaining.drop off.toNat) = remaining :=
    List.take_append_drop _ _
  have hrFinal : FinalRegisters (sliceEnv E src n) dst ctx copy := by
    rcases hr.toFinalRegisters with ⟨h0, h18, h19, h16⟩
    constructor <;> simp_all [sliceEnv, mlir_env]
  have hrTail : (sliceEnv E src n).read (%40) = .value tail := by simp [sliceEnv, tail, off, mlir_env]
  have hrRem : (sliceEnv E src n).read (%39) = .value rem := by simp [sliceEnv, rem, mlir_env]
  have hrCount : (sliceEnv E src n).read (%25) = .value (ctx.add 127#64) := by
    simpa [sliceEnv, mlir_env] using hr.count
  have hstep := slice_block p g E s src n hr.length hr.source hr.shift hr.mask hr.remMask hr.zero hinput
  by_cases hz : q = 0#64
  · have hquot : n.toNat / 128 = 0 := hq.symm.trans (congrArg BitVec.toNat hz)
    have hzoff : off.toNat = 0 := by omega
    have hdone := tail_reaches_final p g sha (sliceEnv E src n) s dst ctx copy tail rem
      completed (remaining.drop off.toNat) mark base hrFinal hrTail hrRem hrCount hwf hout hc
      htail htailRead hrem hne hcc hoc hctx hcopy hframe
    apply ReachesFinal.prepend (by simpa [hzoff] using hdone)
    rw [hstep]
    simp only [show n >>> 7 = 0 from hz, if_pos]
  · have hqpos : 0 < q.toNat := by
      have hnzero : q.toNat ≠ 0 := by intro he; apply hz; exact BitVec.eq_of_toNat_eq he
      omega
    have hqbound : q.toNat < 2 ^ 56 := by have := smallRange_length_lt hinput; omega
    have hblock : SmallRange s.mem src (128 * q.toNat) := smallRange_mono hinput (by omega)
    have hblockRead : readBytes s.mem src (128 * q.toNat) = remaining.take off.toNat := by
      rw [← hread, readBytes_take _ _ _ _ hoff]
      congr 1
      omega
    have hblockLen : (remaining.take off.toNat).length = 128 * q.toNat := by
      rw [List.length_take, hlen, Nat.min_eq_left hoff]
      omega
    obtain ⟨afterBlocks, hcall, he, hc', hwf'⟩ := compress_blocks p.sha512Compress sha hcompress
      s ctx src q completed (remaining.take off.toNat) hwf hc hblock hblockRead hblockLen
      (Or.inl hne) (Or.inl hne) hqpos hqbound (by omega)
    have hout' : OutputResources afterBlocks dst copy :=
      (hout.store _ _).effect he
    have htail' : SmallRange afterBlocks.mem tail rem.toNat := he.smallRange (htail.storeAt _ _)
    have htailRead' : readBytes afterBlocks.mem tail rem.toNat = remaining.drop off.toNat := by
      rw [he.readBytes (htail.storeAt _ _) (show (Range.of (ctx.add 128) 512).Disjoint
          (Range.of tail (8 * rem.toNat)) from Or.inl hne)]
      dsimp only [advanceCount]
      rw [readBytes_storeAt_disjoint _ _ _ _ _ htail (show
        (Range.of (ctx.add 192) 128).Disjoint (Range.of tail (8 * rem.toNat)) from Or.inl hne)]
      exact htailRead
    have hframe' : afterBlocks.mem.eraseFrom mark = base :=
      he.erase_internal mark base (erase_internal_store _ _ _ _ _ hframe hctx) hctx
    let bulk := bulkEnv (sliceEnv E src n) ctx q (s.mem.readAt (ctx.add 192#64) 128)
    have hrFinal' : FinalRegisters bulk dst ctx copy := by
      rcases hrFinal with ⟨h0, h18, h19, h16⟩
      constructor <;> simp_all [bulk, bulkEnv, mlir_env]
    have hdone := tail_reaches_final p g sha bulk afterBlocks dst ctx copy tail rem
      (completed ++ remaining.take off.toNat) (remaining.drop off.toNat) mark base hrFinal'
      (by simpa [bulk, bulkEnv, mlir_env] using hrTail)
      (by simpa [bulk, bulkEnv, mlir_env] using hrRem)
      (by simpa [bulk, bulkEnv, mlir_env] using hrCount)
      hwf' hout' hc' htail' htailRead' hrem hne hcc hoc hctx hcopy hframe'
    apply ReachesFinal.prepend (by simpa [List.append_assoc, hsplit] using hdone)
    rw [hstep]
    simp only [show n >>> 7 ≠ 0 from hz, if_neg]
    exact bulk_block p g (sliceEnv E src n) s afterBlocks ctx src n
      hrFinal.context (by simpa [sliceEnv, mlir_env] using hr.source)
      (by simpa [sliceEnv, mlir_env] using hr.chain)
      (by simpa [sliceEnv, mlir_env] using hr.counter)
      (by simp [sliceEnv, mlir_env]) hc.live (smallRange_length_lt hinput) hcall

end Agave.Ed25519.Verifier.Execution.Challenge

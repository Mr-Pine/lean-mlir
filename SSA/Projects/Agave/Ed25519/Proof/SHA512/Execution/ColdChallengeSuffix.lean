import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.ColdChallengeContext
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.ColdReady
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionSuffix

namespace Agave.Ed25519.Verifier.Execution.Challenge

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open SHA512Finalization (CompressionGlobals CompressionReady CacheFrame CacheOutputEffect)

set_option maxRecDepth 24000
set_option maxHeartbeats 1800000

/-- Exact reachability of the imported bb7, permitting the designated cache
transition in the caller frame while retaining the full transcript context. -/
def ColdReachesFinal (cg : CompressionGlobals) (p : Primitives) (g : Globals)
    (sha : Sha512Model) (E : Env program.Γ) (block : Fin 8) (s : GlobalState)
    (dst ctx copy : Pointer) (input : Bytes) (mark : Nat) (base : MemoryState) : Prop :=
  ∃ F t completed pending,
    (program p g).runFrom E block s = (program p g).runFrom F 7 t ∧
    FinalRegisters F dst ctx copy ∧ ContextRepresents sha t.mem ctx completed pending ∧
    input = completed ++ pending ∧ OutputResources t dst copy ∧ t.WF ∧
    CacheFrame cg base (t.mem.eraseFrom mark) ∧ CompressionReady cg t

theorem ColdReachesFinal.prepend {cg : CompressionGlobals} {p : Primitives}
    {g : Globals} {sha : Sha512Model}
    (h : ColdReachesFinal cg p g sha F next t dst ctx copy input mark base)
    (heq : (program p g).runFrom E block s = (program p g).runFrom F next t) :
    ColdReachesFinal cg p g sha E block s dst ctx copy input mark base := by
  rcases h with ⟨F', t', completed, pending, hrun, hr, hc, hb, ho, hw, hf, hready⟩
  exact ⟨F', t', completed, pending, heq.trans hrun, hr, hc, hb, ho, hw, hf, hready⟩

theorem tail_reaches_final_cold (cg : CompressionGlobals) (p : Primitives) (g : Globals) (compress : Agave.Ed25519.SHA512.Compression)
    (E : Env program.Γ) (s : GlobalState) (dst ctx copy src : Pointer)
    (n : BitVec 64) (completed pending : Bytes) (mark : Nat) (base : MemoryState)
    (hr : FinalRegisters E dst ctx copy)
    (hsrc : E.read (%40) = .value src) (hn : E.read (%39) = .value n)
    (hptr : E.read (%25) = .value (ctx.add 127#64))
    (hwf : s.WF) (hout : OutputResources s dst copy)
    (hc : ChainRepresents (Agave.Ed25519.SHA512.model compress) s.mem ctx completed)
    (hinput : SmallRange s.mem src n.toNat)
    (hread : readBytes s.mem src n.toNat = pending) (hsmall : n.toNat < 128)
    (hne : ctx.id ≠ src.id) (hcc : copy.id ≠ ctx.id) (hoc : dst.id ≠ copy.id)
    (hctx : mark ≤ ctx.id.id) (hcopy : mark ≤ copy.id.id)
    (hframe : CacheFrame cg base (s.mem.eraseFrom mark))
    (hready : CompressionReady cg s) (hctxK : ctx.id ≠ cg.constants)
    (hctxCache : ctx.id ≠ cg.cache) :
    ColdReachesFinal cg p g (Agave.Ed25519.SHA512.model compress) E 6 s dst ctx copy (completed ++ pending) mark base := by
  have hlen : pending.length = n.toNat := by rw [← hread, readBytes_length]
  have hcontext : ContextRepresents (Agave.Ed25519.SHA512.model compress) (tailState s ctx src n).mem ctx completed pending := by
    dsimp only [tailState]
    rw [← hlen]
    exact finish_context (Agave.Ed25519.SHA512.model compress) s.mem ctx src completed pending hc
      (by simpa [hlen] using hinput) (by simpa [hlen] using hread) (by omega) hne
  have hr' : FinalRegisters (tailEnv E n) dst ctx copy := by
    rcases hr with ⟨h0, h18, h19, h16⟩
    constructor <;> simp_all [tailEnv, mlir_env]
  have hframe' : CacheFrame cg base ((tailState s ctx src n).mem.eraseFrom mark) :=
    (hframe.internal_store (ctx.add 127#64) (BitVec.ofNat 8 n.toNat) hctx).internal_store ctx _ hctx
  have hready' : CompressionReady cg (tailState s ctx src n) :=
    CompressionReady.storeAt cg _ ctx _
      (CompressionReady.storeAt cg s (ctx.add 127#64) (BitVec.ofNat 8 n.toNat)
        hready hctxK hctxCache) hctxK hctxCache
  exact ⟨tailEnv E n, tailState s ctx src n, completed, pending,
    tail_block p g E s ctx src n hr.context hsrc hn hptr hc.live hinput hsmall hne,
    hr', hcontext, rfl, (hout.store _ _).store _ _, hwf.storeAt.storeAt, hframe', hready'⟩

theorem remaining_reaches_final_cold (cg : CompressionGlobals) (p : Primitives) (g : Globals) (compress : Agave.Ed25519.SHA512.Compression)
    (hcompress : SHA512Finalization.CompressContractUnder cg p.sha512Compress compress)
    (E : Env program.Γ) (s : GlobalState) (dst ctx copy src : Pointer)
    (n : BitVec 64) (completed remaining : Bytes) (mark : Nat) (base : MemoryState)
    (hr : RemainingRegisters E dst ctx copy src n) (hwf : s.WF)
    (hout : OutputResources s dst copy) (hc : ChainRepresents (Agave.Ed25519.SHA512.model compress) s.mem ctx completed)
    (hinput : SmallRange s.mem src n.toNat)
    (hread : readBytes s.mem src n.toNat = remaining)
    (hcount : completed.length / 128 + n.toNat / 128 < 2 ^ 128)
    (hne : ctx.id ≠ src.id) (hcc : copy.id ≠ ctx.id) (hoc : dst.id ≠ copy.id)
    (hctx : mark ≤ ctx.id.id) (hcopy : mark ≤ copy.id.id)
    (hframe : CacheFrame cg base (s.mem.eraseFrom mark))
    (hready : CompressionReady cg s) (hctxK : ctx.id ≠ cg.constants)
    (hctxCache : ctx.id ≠ cg.cache) (hsrcCache : src.id ≠ cg.cache)
    (houtCache : dst.id ≠ cg.cache) (hcopyCache : copy.id ≠ cg.cache)
    (hcache : cg.cache.id < mark) :
    ColdReachesFinal cg p g (Agave.Ed25519.SHA512.model compress) E 3 s dst ctx copy (completed ++ remaining) mark base := by
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
    have hdone := tail_reaches_final_cold cg p g compress (sliceEnv E src n) s dst ctx copy tail rem
      completed (remaining.drop off.toNat) mark base hrFinal hrTail hrRem hrCount hwf hout hc
      htail htailRead hrem hne hcc hoc hctx hcopy hframe hready hctxK hctxCache
    apply ColdReachesFinal.prepend (by simpa [hzoff] using hdone)
    rw [hstep]
    split
    · rfl
    · rename_i hneZero
      exact False.elim (hneZero hz)
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
    obtain ⟨afterBlocks, hcall, he, hc', hwf', hrAfter⟩ := compress_blocks_cold cg p.sha512Compress compress hcompress
      s ctx src q completed (remaining.take off.toNat) hwf hc hblock hblockRead hblockLen
      (Or.inl hne) (Or.inl hne) hqpos hqbound (by omega) hready hctxK hctxCache hsrcCache
    have hout' : OutputResources afterBlocks dst copy :=
      ⟨he.smallRange dst 32 houtCache (hout.output.storeAt _ _),
        he.smallRange copy 208 hcopyCache (hout.copy.storeAt _ _)⟩
    have htail' : SmallRange afterBlocks.mem tail rem.toNat := he.smallRange tail rem.toNat hsrcCache (htail.storeAt _ _)
    have htailRead' : readBytes afterBlocks.mem tail rem.toNat = remaining.drop off.toNat := by
      rw [he.readBytes tail rem.toNat hsrcCache (htail.storeAt _ _) (show (Range.of (ctx.add 128) 512).Disjoint
          (Range.of tail (8 * rem.toNat)) from Or.inl hne)]
      dsimp only [advanceCount]
      rw [readBytes_storeAt_disjoint _ _ _ _ _ htail (show
        (Range.of (ctx.add 192) 128).Disjoint (Range.of tail (8 * rem.toNat)) from Or.inl hne)]
      exact htailRead
    have hframe' : CacheFrame cg base (afterBlocks.mem.eraseFrom mark) :=
      (hframe.internal_store (ctx.add 192#64) (s.mem.readAt (ctx.add 192#64) 128 + q.setWidth 128) hctx).trans (he.erase_internal mark hcache hctx)
    let bulk := bulkEnv (sliceEnv E src n) ctx q (s.mem.readAt (ctx.add 192#64) 128)
    have hrFinal' : FinalRegisters bulk dst ctx copy := by
      rcases hrFinal with ⟨h0, h18, h19, h16⟩
      constructor <;> simp_all [bulk, bulkEnv, mlir_env]
    have hdone := tail_reaches_final_cold cg p g compress bulk afterBlocks dst ctx copy tail rem
      (completed ++ remaining.take off.toNat) (remaining.drop off.toNat) mark base hrFinal'
      (by simpa [bulk, bulkEnv, mlir_env] using hrTail)
      (by simpa [bulk, bulkEnv, mlir_env] using hrRem)
      (by simpa [bulk, bulkEnv, mlir_env] using hrCount)
      hwf' hout' hc' htail' htailRead' hrem hne hcc hoc hctx hcopy hframe' hrAfter hctxK hctxCache
    apply ColdReachesFinal.prepend (by simpa [List.append_assoc, hsplit] using hdone)
    rw [hstep]
    split
    · rename_i heZero
      exact False.elim (hz heZero)
    · skip
      exact bulk_block p g (sliceEnv E src n) s afterBlocks ctx src n
        hrFinal.context (by simpa [sliceEnv, mlir_env] using hr.source)
        (by simpa [sliceEnv, mlir_env] using hr.chain)
        (by simpa [sliceEnv, mlir_env] using hr.counter)
        (by simp [sliceEnv, mlir_env]) hc.live (smallRange_length_lt hinput) hcall


end Agave.Ed25519.Verifier.Execution.Challenge

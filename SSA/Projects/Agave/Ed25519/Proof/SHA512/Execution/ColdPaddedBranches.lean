import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.ColdBranchContracts
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.PaddedBranches
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Locals

namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Challenge
open Agave.Ed25519.SHA512

/-- The branch result records the exact final compression state and the
private-frame invariant needed to invoke the contextual reducer later. -/
structure ColdPaddedResult (g : CompressionGlobals) (p : Primitives) (compress : Compression) (entry s : GlobalState)
    (E : Env program.Γ) (out : Pointer) (pending : Bytes) (total : Nat)
    (long : Bool) (after : GlobalState) : Prop where
  run : (program p).runFrom E (if long then 1 else 2) s =
    (program p).runFrom (branchEnv E entry long) 3 after
  chain : after.mem.readAt ((slot entry 5).add 128#64) 512 =
    (finalBlocks pending total).foldl compress.run
      (s.mem.readAt ((slot entry 5).add 128#64) 512)
  locals : LocalsLive entry after.mem
  output : SmallRange after.mem out 32
  frame : CacheFrame g entry.mem (after.mem.eraseFrom entry.alloc.nextFreeBlock)
  counter : s.alloc.nextFreeBlock ≤ after.alloc.nextFreeBlock
  wf : after.WF
  ready : CompressionReady g after

set_option maxRecDepth 20000
set_option maxHeartbeats 1800000

/-- Refine the actual branch byte inputs into the SHA padding specification.
Only the one-block primitive contract is used, once or twice according to
the actual pending-count test. -/
theorem padded_branches_cold (g : CompressionGlobals) (p : Primitives) (compress : Compression)
    (hcompress : OneBlockCompressContractUnder g p.sha512Compress compress)
    (entry s : GlobalState) (E : Env program.Γ) (out : Pointer)
    (pending : Bytes) (total : Nat) (long : Bool)
    (hchoice : long = true ↔ 112 ≤ pending.length)
    (hp : pending.length < 128)
    (hbuffer : E.read (%84) = .value (slot entry 3))
    (hfirst : E.read (%83) = .value (slot entry 2))
    (hlast : E.read (%82) = .value (slot entry 1))
    (hshort : E.read (%81) = .value (slot entry 0))
    (hchain : E.read (%151) = .value ((slot entry 5).add 128#64))
    (hlength : E.read (%161) = .value (swapBytes (BitVec.ofNat 128 (8 * total))))
    (h112 : E.read (%10) = .value 112#64)
    (h128 : E.read (%2) = .value 128#64)
    (h1 : E.read (%12) = .value 1#64) (h0 : E.read (%8) = .value 0#8)
    (hwf : s.WF) (hl : LocalsLive entry s.mem) (ho : SmallRange s.mem out 32)
    (hbytes : readBytes s.mem (slot entry 3) 128 = firstPaddingBlock pending)
    (hframe : CacheFrame g entry.mem (s.mem.eraseFrom entry.alloc.nextFreeBlock))
    (hready : CompressionReady g s)
    (hcache : g.cache.id < entry.alloc.nextFreeBlock)
    (hconstants : g.constants.id < entry.alloc.nextFreeBlock)
    (houtCache : out.id ≠ g.cache) :
    ∃ after, ColdPaddedResult g p compress entry s E out pending total long after := by
  have hc := smallRange_add hl.context (k := 128) (count := 64) (by decide)
  have internal (i : Nat) (hi : i ≤ 70) := slot_internal entry i hi
  have ne (i j : Nat) (hi : i ≤ 70) (hj : j ≤ 70) (hne : i ≠ j) :=
    slot_ne entry i j hi hj hne
  have nk (i : Nat) (hi : i ≤ 70) := slot_ne_global entry i hi g.constants hconstants
  have nb (i : Nat) (hi : i ≤ 70) := slot_ne_global entry i hi g.cache hcache
  cases hlong : long with
  | false =>
    have hs : pending.length < 112 := by simp [hlong] at hchoice; omega
    obtain ⟨after, hrun, heRaw, ha, hra⟩ := short_block_cold g p compress hcompress E s
      (slot entry 3) (slot entry 0) ((slot entry 5).add 128#64) _
      hbuffer hshort hchain hlength h112 h128 h1 hwf hl.buffer hl.block0 hc
      (ne 0 3 (by decide) (by decide) (by decide))
      (ne 3 5 (by decide) (by decide) (by decide))
      (ne 0 5 (by decide) (by decide) (by decide))
      hready (nk 5 (by decide)) (nb 5 (by decide))
      (nk 3 (by decide)) (nb 3 (by decide)) (nk 0 (by decide)) (nb 0 (by decide))
    have he := heRaw.cacheOutput hra (nb 5 (by decide))
    have hb := short_padding_readback s (slot entry 3) pending total hl.buffer hbytes hs
    have hf : CacheFrame g entry.mem
        ((copyBlock (writeLength s (slot entry 3) (swapBytes (BitVec.ofNat 128 (8 * total))))
          (slot entry 3) (slot entry 0)).mem.eraseFrom entry.alloc.nextFreeBlock) :=
      (hframe.internal_store ((slot entry 3).add 112#64)
        (swapBytes (BitVec.ofNat 128 (8 * total))) (internal 3 (by decide))).internal_store
          (slot entry 0) _ (internal 0 (by decide))
    refine ⟨after, ?_⟩
    constructor
    · simpa [branchEnv] using hrun
    · have hfit : Fits (copyBlock (writeLength s (slot entry 3)
          (swapBytes (BitVec.ofNat 128 (8 * total)))) (slot entry 3) (slot entry 0)).mem
          ((slot entry 5).add 128#64) 512 := ((hc.storeAt _ _).storeAt _ _).fits
      rw [he.output (nb 5 (by decide)) hfit, hb]
      simp [finalBlocks, hs]
    · exact ((hl.storeAt _ _).storeAt _ _).cacheEffect he hcache
    · exact he.smallRange out 32 houtCache ((ho.storeAt _ _).storeAt _ _)
    · exact hf.trans (he.erase_internal entry.alloc.nextFreeBlock hcache (internal 5 (by decide)))
    · exact he.counter
    · exact ha
    · exact hra
  | true =>
    have hs : ¬ pending.length < 112 := by have := hchoice.mp hlong; omega
    obtain ⟨middle, after, hrun, he1Raw, he2Raw, ha, hrm, hra⟩ := long_block_cold g p compress
      hcompress E s (slot entry 3) (slot entry 2) (slot entry 1)
      ((slot entry 5).add 128#64) _ hbuffer hfirst hlast hchain hlength h112 h128 h1 h0
      hwf hl.buffer hl.block2 hl.block1 hc
      (ne 2 3 (by decide) (by decide) (by decide))
      (ne 1 3 (by decide) (by decide) (by decide))
      (ne 3 5 (by decide) (by decide) (by decide))
      (ne 2 5 (by decide) (by decide) (by decide))
      (ne 1 5 (by decide) (by decide) (by decide))
      hready (nk 5 (by decide)) (nb 5 (by decide)) (nk 3 (by decide)) (nb 3 (by decide))
      (nk 2 (by decide)) (nb 2 (by decide)) (nk 1 (by decide)) (nb 1 (by decide))
    have he1 := he1Raw.cacheOutput hrm (nb 5 (by decide))
    have he2 := he2Raw.cacheOutput hra (nb 5 (by decide))
    have hmid := (hl.storeAt (slot entry 2) (s.mem.readAt (slot entry 3) 1024)).cacheEffect he1 hcache
    have hmout := he1.smallRange out 32 houtCache (ho.storeAt (slot entry 2) (s.mem.readAt (slot entry 3) 1024))
    have hmc := smallRange_add hmid.context (k := 128) (count := 64) (by decide)
    have hb := long_padding_readback middle (slot entry 3) total hmid.buffer
    have hfmid : CacheFrame g entry.mem (middle.mem.eraseFrom entry.alloc.nextFreeBlock) :=
      (hframe.internal_store (slot entry 2) (s.mem.readAt (slot entry 3) 1024) (internal 2 (by decide))).trans
        (he1.erase_internal entry.alloc.nextFreeBlock hcache (internal 5 (by decide)))
    have hf : CacheFrame g entry.mem
        ((copyBlock (writeLength (clearPrefix middle (slot entry 3))
          (slot entry 3) (swapBytes (BitVec.ofNat 128 (8 * total))))
          (slot entry 3) (slot entry 1)).mem.eraseFrom entry.alloc.nextFreeBlock) :=
      ((hfmid.internal_store (slot entry 3) 0#896 (internal 3 (by decide))).internal_store
        ((slot entry 3).add 112#64) (swapBytes (BitVec.ofNat 128 (8 * total)))
        (internal 3 (by decide))).internal_store (slot entry 1) _ (internal 1 (by decide))
    refine ⟨after, ?_⟩
    constructor
    · simpa [branchEnv] using hrun
    · have hfit : Fits (copyBlock (writeLength (clearPrefix middle (slot entry 3))
          (slot entry 3) (swapBytes (BitVec.ofNat 128 (8 * total))))
          (slot entry 3) (slot entry 1)).mem ((slot entry 5).add 128#64) 512 :=
        (((hmc.storeAt _ _).storeAt _ _).storeAt _ _).fits
      rw [he2.output (nb 5 (by decide)) hfit, hbytes, hb]
      simp [finalBlocks, hs]
    · exact (((hmid.storeAt _ _).storeAt _ _).storeAt _ _).cacheEffect he2 hcache
    · exact he2.smallRange out 32 houtCache (((hmout.storeAt _ _).storeAt _ _).storeAt _ _)
    · exact hf.trans (he2.erase_internal entry.alloc.nextFreeBlock hcache (internal 5 (by decide)))
    · exact Nat.le_trans he1.counter he2.counter
    · exact ha
    · exact hra

end Agave.Ed25519.Verifier.Execution.SHA512Finalization

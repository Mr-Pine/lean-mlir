import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionControl
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionGlobals
import SSA.Projects.Agave.Ed25519.Bridge.Acceptance

/-!
The exact incremental SHA-512 ABI at the two external calls made by the
extracted challenge body. The contracts here are deliberately local: neither
mentions `Challenge.program`, the verifier, nor a challenge result equality.

Compression operates on complete 128-byte blocks and the 64-byte chaining
state. `scalar_from_sha512` receives the full 208-byte context. It owns SHA-512
padding, final compression, digest serialization, and reduction of the
little-endian 64-byte digest modulo the Ed25519 subgroup order. These operations
are not present in the extracted `challenge_scalar` body.
-/

namespace Agave.Ed25519.Verifier.Execution.Challenge

open LeanMLIR.RIR
open Agave.Ed25519.Bridge Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Reduce64.Execution

/-- Canonical encoding of the digest's little-endian integer modulo L.
This module does not import the legacy SLLVM SHA interface. -/
def digestScalarBytes (digest : BitVec 512) : BitVec 256 :=
  BitVec.ofNat 256 (digest.toNat % subgroupOrder)

theorem digestScalarBytes_toNat (digest : BitVec 512) :
    (digestScalarBytes digest).toNat = digest.toNat % subgroupOrder := by
  have h : digest.toNat % subgroupOrder < 2 ^ 256 :=
    lt_trans (Nat.mod_lt _ (by norm_num [subgroupOrder])) (by norm_num [subgroupOrder])
  exact Nat.mod_eq_of_lt h

/-- A byte-level memory observation; the separate `SmallRange` hypotheses
require every observed byte to belong to a live allocation. -/
def readBytes (m : MemoryState) (p : Pointer) (n : Nat) : Bytes :=
  List.ofFn fun i : Fin n => m.readAt (p.add (BitVec.ofNat 64 i.val)) 8

@[simp] theorem readBytes_length (m : MemoryState) (p : Pointer) (n : Nat) :
    (readBytes m p n).length = n := by
  simp [readBytes]

theorem readBytes_append (m : MemoryState) (p : Pointer) (n k : Nat) :
    readBytes m p (n + k) =
      readBytes m p n ++ readBytes m (p.add (BitVec.ofNat 64 n)) k := by
  simp only [readBytes, List.ofFn_add]
  congr 2
  funext i
  simp [Pointer.add_add, BitVec.ofNat_add]

/-- A bulk little-endian memory read observes exactly the same byte sequence
as reading the successive addresses. This discharges byte order for memcpy. -/
theorem readBytes_eq_bytesOf (m : MemoryState) (p : Pointer) (n : Nat)
    (hr : SmallRange m p n) :
    readBytes m p n = bytesOf (m.readAt p (n * 8)) := by
  unfold readBytes bytesOf
  congr 1
  funext i
  have hi : i.val < 2 ^ 64 := by
    have := hr.offset_lt
    have := i.isLt
    norm_num at *
    omega
  have hf : Fits m p (n * 8) := by simpa [Nat.mul_comm] using hr.fits
  have hbyte : (BitVec.ofNat 64 i.val).toNat * 8 + 8 ≤ n * 8 := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]
    omega
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi] using
    MemoryState.readAt_add_of_readAt hf (hr.no_wrap (by omega)) hbyte rfl

theorem readBytes_storeAt_self (m : MemoryState) (p : Pointer) (n : Nat)
    (hr : SmallRange m p n) (value : BitVec (n * 8)) :
    readBytes (m.storeAt p value) p n = bytesOf value := by
  rw [readBytes_eq_bytesOf _ _ _ (hr.storeAt p value),
    MemoryState.readAt_storeAt_self (by simpa [Nat.mul_comm] using hr.fits)]

/-- A bulk copy preserves every subrange at the same relative byte offset.
The source is observed before the store, exactly as in RIR `memcpy`. -/
theorem copy_readAt_offset (m : MemoryState) (src dst : Pointer)
    (bytes offset count : Nat)
    (hsrc : SmallRange m src bytes) (hdst : SmallRange m dst bytes)
    (hrange : offset + count ≤ bytes) :
    (m.storeAt dst (m.readAt src (8 * bytes))).readAt
      (dst.add (BitVec.ofNat 64 offset)) (8 * count) =
      m.readAt (src.add (BitVec.ofNat 64 offset)) (8 * count) := by
  have hoff : offset < 2 ^ 64 := by
    have := hsrc.offset_lt
    norm_num at *
    omega
  have hbits : (BitVec.ofNat 64 offset).toNat * 8 + 8 * count ≤ 8 * bytes := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff]
    omega
  rw [MemoryState.readAt_storeAt_add hdst.fits (hdst.no_wrap (by omega)) hbits]
  exact (MemoryState.readAt_add_of_readAt hsrc.fits (hsrc.no_wrap (by omega)) hbits rfl).symm

/-- Abstract SHA operations used solely to state the external contracts.
`compress` processes a byte string of full blocks; `digest` includes padding
and serializes all 64 digest bytes in their output order. -/
structure Sha512Model where
  compress : BitVec 512 → Bytes → BitVec 512
  digest : Bytes → BitVec 512
  empty : ∀ state, compress state [] = state
  append : ∀ state xs ys, xs.length % 128 = 0 → ys.length % 128 = 0 →
    compress state (xs ++ ys) = compress (compress state xs) ys

def initialWords : BitVec 512 := sha512InitialState.bytes

/-- The actual Rust `Sha512` context layout at the scalar finalization call:
127 buffer bytes, one byte of buffer length, eight native u64 chaining words,
and a u128 count of already-compressed blocks. Unused buffer bytes are ignored.
`completed` excludes `pending`, which is not compressed until finalization. -/
structure ContextRepresents (sha : Sha512Model) (m : MemoryState) (ctx : Pointer)
    (completed pending : Bytes) : Prop where
  live : SmallRange m ctx 208
  completedWhole : completed.length % 128 = 0
  pendingBound : pending.length < 128
  pendingBytes : readBytes m ctx pending.length = pending
  pendingCount : (m.readAt (ctx.add 127) 8).toNat = pending.length
  chaining : m.readAt (ctx.add 128) 512 = sha.compress initialWords completed
  blockCount : (m.readAt (ctx.add 192) 128).toNat = completed.length / 128

/-- The extracted final block copies all 208 bytes before passing the
context to scalar reduction. Its meaningful fields survive that exact copy,
including the unused-buffer distinction in the source ABI. -/
theorem ContextRepresents.copy (sha : Sha512Model) (m : MemoryState)
    (src dst : Pointer) (completed pending : Bytes)
    (hctx : ContextRepresents sha m src completed pending)
    (hdst : SmallRange m dst 208) :
    ContextRepresents sha (m.storeAt dst (m.readAt src 1664)) dst completed pending := by
  refine ⟨hdst.storeAt _ _, hctx.completedWhole, hctx.pendingBound, ?_, ?_, ?_, ?_⟩
  · calc
      readBytes (m.storeAt dst (m.readAt src 1664)) dst pending.length =
          readBytes m src pending.length := by
        unfold readBytes
        congr 1
        funext i
        simpa using copy_readAt_offset m src dst 208 i.val 1 hctx.live hdst (by
          have := i.isLt
          have := hctx.pendingBound
          omega)
      _ = pending := hctx.pendingBytes
  · have hc := copy_readAt_offset m src dst 208 127 1 hctx.live hdst (by decide)
    exact (congrArg BitVec.toNat hc).trans hctx.pendingCount
  · have hc := copy_readAt_offset m src dst 208 128 64 hctx.live hdst (by decide)
    exact hc.trans hctx.chaining
  · have hc := copy_readAt_offset m src dst 208 192 16 hctx.live hdst (by decide)
    exact (congrArg BitVec.toNat hc).trans hctx.blockCount

/-- Primitive calls may advance the allocation counter, but their complete
observable memory effect is a single store. This permits internal stack
allocation followed by the RIR call-frame cleanup. -/
structure StoreEffect (before after : GlobalState) (dst : Pointer) (value : BitVec w) : Prop where
  memory : after.mem = before.mem.storeAt dst value
  counter : before.alloc.nextFreeBlock ≤ after.alloc.nextFreeBlock

theorem StoreEffect.wellFormed (h : StoreEffect before after dst value)
    (hwf : before.WF) : after.WF := by
  obtain ⟨hm, hc⟩ := h
  rw [GlobalState.WF]
  intro k hk
  rw [hm] at hk
  have hs := GlobalState.WF.storeAt (p := dst) (x := value) hwf
  have hb := hs k hk
  exact lt_of_lt_of_le hb hc

/-- Contract for only `sha512::compress512`. It neither updates the caller's
block counter nor reads the partial-buffer length. The source may share the
context allocation, but must be disjoint from the chaining-state bytes. -/
def CompressContract
    (compressCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (sha : Sha512Model) : Prop :=
  ∀ (state : GlobalState) (chain data : Pointer) (count : BitVec 64),
    state.WF → SmallRange state.mem chain 64 →
    SmallRange state.mem data (128 * count.toNat) →
    (Range.of chain 512).Disjoint (Range.of data (8 * (128 * count.toNat))) →
    0 < count.toNat → count.toNat < 2 ^ 56 →
    ∃ after,
      compressCall (.cons (.value chain) (.cons (.value data)
        (.cons (.value count) .nil))) state = .value (.nil, after) ∧
      StoreEffect state after chain
        (sha.compress (state.mem.readAt chain 512)
          (readBytes state.mem data (128 * count.toNat)))

/-- Contract for only `scalar_from_sha512`, including SHA padding/finalization
and digest reduction. The digest is interpreted as little-endian bytes, even
though SHA-512's internal rounds use big-endian message words. -/
def ScalarFromSha512Contract
    (scalarCall : Vals [.ptr, .ptr] → EffectM (Vals []))
    (sha : Sha512Model) : Prop :=
  ∀ (state : GlobalState) (dst ctx : Pointer) (completed pending : Bytes),
    state.WF → SmallRange state.mem dst 32 →
    ContextRepresents sha state.mem ctx completed pending →
    (Range.of dst 256).Disjoint (Range.of ctx 1664) →
    ∃ after,
      scalarCall (.cons (.value dst) (.cons (.value ctx) .nil)) state =
        .value (.nil, after) ∧
      StoreEffect state after dst (digestScalarBytes (sha.digest (completed ++ pending)))

/-- The bytes written by the scalar primitive have the precise mathematical
meaning needed by the verifier. This is a consequence of the local callee
contract and the already-proved digest byte-order/reduction lemmas. -/
theorem scalar_contract_output
    (scalarCall : Vals [.ptr, .ptr] → EffectM (Vals [])) (sha : Sha512Model)
    (hcall : ScalarFromSha512Contract scalarCall sha)
    (state : GlobalState) (dst ctx : Pointer) (completed pending : Bytes)
    (hwf : state.WF) (hdst : SmallRange state.mem dst 32)
    (hctx : ContextRepresents sha state.mem ctx completed pending)
    (hdisjoint : (Range.of dst 256).Disjoint (Range.of ctx 1664)) :
    ∃ after,
      scalarCall (.cons (.value dst) (.cons (.value ctx) .nil)) state =
        .value (.nil, after) ∧
      (after.mem.readAt dst 256).toNat =
        (sha.digest (completed ++ pending)).toNat % subgroupOrder ∧
      after.WF := by
  obtain ⟨after, hc, heffect⟩ := hcall state dst ctx completed pending hwf hdst hctx hdisjoint
  refine ⟨after, hc, ?_, heffect.wellFormed hwf⟩
  rw [heffect.memory, MemoryState.readAt_storeAt_self hdst.fits, digestScalarBytes_toNat]

end Agave.Ed25519.Verifier.Execution.Challenge

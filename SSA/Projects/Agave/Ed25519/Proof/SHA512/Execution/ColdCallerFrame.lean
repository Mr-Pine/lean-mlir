import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.ColdFrame

namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Challenge

/-- Every caller observation needed after challenge computation. The key's
whole decoded-key allocation, both signature halves, and the message remain
live and byte-for-byte unchanged; the SHA cache itself is deliberately absent. -/
structure ChallengeCallerRegions (before after : GlobalState)
    (key signature message : Pointer) (messageBytes : Nat) : Prop where
  keyLive : SmallRange after.mem key 192
  signatureLive : SmallRange after.mem signature 64
  messageLive : SmallRange after.mem message messageBytes
  keyRead : after.mem.readAt key 1536 = before.mem.readAt key 1536
  signatureRead : after.mem.readAt signature 512 = before.mem.readAt signature 512
  messageRead : readBytes after.mem message messageBytes = readBytes before.mem message messageBytes

/-- This narrower frame is sufficient for a caller's final Boolean path.
It neither requires nor asserts preservation of the mutable SHA cache. -/
structure CacheAwareOutputFrame (g : CompressionGlobals) (before after : GlobalState)
    (out : Pointer) (bytes : Nat) : Prop where
  wellFormed : after.WF
  live : ∀ ptr count, ptr.id ≠ g.cache → SmallRange before.mem ptr count →
    SmallRange after.mem ptr count
  read : ∀ ptr width, ptr.id ≠ g.cache →
    (Range.of ptr width).Disjoint (Range.of out (8 * bytes)) →
    after.mem.readAt ptr width = before.mem.readAt ptr width
  cache : CacheTransition (before.mem.readAt g.cachePtr 8) (after.mem.readAt g.cachePtr 8)

theorem CacheOutputEffect.callerFrame
    (he : CacheOutputEffect g before after out (value : BitVec (8 * bytes)))
    (hwf : before.WF) (hr : CompressionReady g before) (ho : out.id ≠ g.cache) :
    CacheAwareOutputFrame g before after out bytes := by
  refine ⟨he.wellFormed hr hwf, fun ptr count hp hl => he.smallRange ptr count hp hl,
    fun ptr width hp hd => he.read ptr width hp hd.symm, ?_⟩
  simpa only [MemoryState.readAt_storeAt_disjoint (p := out) (q := g.cachePtr) (Range.disjoint_of_id_ne ho) value] using he.memory.transition

theorem CacheAwareOutputFrame.readBytes
    (hf : CacheAwareOutputFrame g before after out bytes)
    (ptr : Pointer) (count : Nat) (value : BitVec (8 * count))
    (hread : Dalek.ReadBytes before ptr count value) (hp : ptr.id ≠ g.cache)
    (hd : (Range.of ptr (8 * count)).Disjoint (Range.of out (8 * bytes))) :
    Dalek.ReadBytes after ptr count value :=
  ⟨hf.live ptr count hp hread.1, (hf.read ptr (8 * count) hp hd).trans hread.2⟩

/-- Exact preservation of all caller regions used by Dalek's post-challenge
scalar multiplication, compression, and comparison path. -/
theorem CacheOutputEffect.challenge_regions
    (he : CacheOutputEffect g before after out (value : BitVec 256))
    (key signature message : Pointer) (count : Nat)
    (hk : SmallRange before.mem key 192) (hs : SmallRange before.mem signature 64)
    (hm : SmallRange before.mem message count)
    (hkc : key.id ≠ g.cache) (hsc : signature.id ≠ g.cache) (hmc : message.id ≠ g.cache)
    (hok : (Range.of out 256).Disjoint (Range.of key 1536))
    (hos : (Range.of out 256).Disjoint (Range.of signature 512))
    (hom : (Range.of out 256).Disjoint (Range.of message (8 * count))) :
    ChallengeCallerRegions before after key signature message count :=
  ⟨he.smallRange key 192 hkc hk, he.smallRange signature 64 hsc hs,
    he.smallRange message count hmc hm,
    he.read key 1536 hkc hok, he.read signature 512 hsc hos,
    he.readBytes message count hmc hm hom⟩

/-- Any Boolean predicate of the scalar output and preserved caller regions
has the same input values for cold and warm SHA dispatch. This is a memory
observation theorem, not a replacement assumption for verifier execution. -/
theorem CacheOutputEffect.challenge_boolean
    (he : CacheOutputEffect g before after out (value : BitVec 256))
    (key signature message : Pointer) (count : Nat)
    (ho : SmallRange before.mem out 32) (hoc : out.id ≠ g.cache)
    (hregions : ChallengeCallerRegions before after key signature message count)
    (observe : BitVec 256 → BitVec 1536 → BitVec 512 → Bytes → Bool) :
    observe (after.mem.readAt out 256) (after.mem.readAt key 1536)
      (after.mem.readAt signature 512) (Challenge.readBytes after.mem message count) =
    observe value (before.mem.readAt key 1536)
      (before.mem.readAt signature 512) (Challenge.readBytes before.mem message count) := by
  rw [he.output hoc ho.fits, hregions.keyRead, hregions.signatureRead, hregions.messageRead]

end Agave.Ed25519.Verifier.Execution.SHA512Finalization

import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionLeaves
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekChallengeLinked

/-!
# Exact Dalek execution from the linked challenge and remaining leaves

The SHA IV is required only in this invocation's initial memory and is
preserved through entry allocation. No universal IV availability or whole
challenge/verifier execution contract is assumed.
-/
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

theorem program_from_entry_of_leaf_contracts {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (contracts : LeafContracts p g layout shared doubleBase compress)
    (cp : Challenge.Primitives) (cg : Challenge.Globals) (sha : Challenge.Sha512Model)
    (hlink : p.challengeScalar = (Challenge.program cp cg).call)
    (hcompress : Challenge.CompressContract cp.sha512Compress sha)
    (hscalar : Challenge.ScalarFromSha512Contract cp.scalarFromSha512 sha)
    (hencoding : ∀ r a msg, layout.scalar (challenge r a msg) =
      Challenge.digestScalarBytes (sha.digest (Challenge.transcript r a msg)))
    (hidentity : layout.identity = identityBytes)
    (E : Env program.Γ) (initial : GlobalState) (key signature message : Pointer)
    (a r bytes : Bytes32) (minusA : Point) (msg : List (BitVec 8))
    (hkeyE : E.read (%arg0) = .value key)
    (hsigE : E.read (%arg1) = .value signature)
    (hmsgE : E.read (%arg2) = .value message)
    (hlenE : E.read (%arg3) = .value (BitVec.ofNat 64 msg.length))
    (hwf : initial.WF) (hk : SmallRange initial.mem key 192)
    (hsig : SmallRange initial.mem signature 64)
    (hmsg : SmallRange initial.mem message msg.length)
    (ha : initial.mem.readAt key 256 = a)
    (hr : initial.mem.readAt signature 256 = r)
    (hs : initial.mem.readAt (signature.add 32#64) 256 = bytes)
    (hA : ReadBytes initial (key.add 32#64) 160 (layout.point minusA))
    (hmbytes : ∀ (i : Nat) (hi : i < msg.length),
      initial.mem.readAt (message.add (BitVec.ofNat 64 i)) 8 = msg[i])
    (hmlen : msg.length < 2^63)
    (hglobal : ReadBytes initial g.address0 40 (1#320))
    (hcache : SmallRange initial.mem g.address1 1)
    (hkeyCache : (Range.of (key.add 32#64) 1280).Disjoint (Range.of g.address1 8))
    (hsigCache : (Range.of signature 256).Disjoint (Range.of g.address1 8))
    (hiv : ReadBytes initial cg.address0 64 Challenge.initialWords) :
    ∃ after, (program p g).runFrom E 0 initial =
      .value (.cons (.value (code (prehashed shared doubleBase compress minusA r bytes
        (challenge r a msg)))) .nil, after) := by
  obtain ⟨challenged, multiplied, compared, hc, hchallenge, hm, he, hentry⟩ :=
    entry_of_sha_contracts p g layout shared challenge cp cg sha hlink hcompress hscalar
      hencoding contracts.pointMulByPow2
      contracts.pointConstantTimeEq hidentity E initial key signature message a r minusA msg
      hkeyE hsigE hmsgE hlenE hwf hk hsig hmsg ha hr hA hmbytes hmlen hglobal hiv
  have hrbytes : ReadBytes initial signature 32 r :=
    ⟨by simpa only [Pointer.add_zero] using smallRange_add hsig (k := 0) (count := 32) (by decide), hr⟩
  have hsbytes : ReadBytes initial (signature.add 32#64) 32 bytes :=
    ⟨smallRange_add hsig (k := 32) (count := 32) (by decide), hs⟩
  by_cases hsmall : shared.smallOrder minusA = true
  · refine ⟨compared, ?_⟩
    rw [hentry, hsmall]
    have hret := return_block p g ((entryEnv E g initial key true)[%71 := .value 2#8])
      compared 2#8 (by simp [mlir_env])
    simpa [prehashed, hsmall, code] using hret
  · have hfalse : shared.smallOrder minusA = false := by
      cases h : shared.smallOrder minusA with
      | false => rfl
      | true => exact False.elim (hsmall h)
    have hregs := entry_body_registers E initial key signature g false hsigE
    have hmemory := entry_body_memory initial challenged multiplied compared hwf key signature g
      layout (challenge r a msg) minusA r bytes hc hchallenge hm he hA hsig hrbytes hsbytes hglobal hcache
    have hdisjoint := entry_body_disjoint initial hwf key signature g hA.1 hsig hglobal.1
      hcache hkeyCache hsigCache
    obtain ⟨after, hbody⟩ := body_of_leaf_contracts p g layout shared doubleBase compress
      contracts hidentity (entryTailPointers initial key signature g) (entryPointPointers initial g)
      (stackSlot initial 0) rfl (entryEnv E g initial key false) compared (challenge r a msg)
      minusA r bytes hregs hmemory hdisjoint
    have hspec : prehashed shared doubleBase compress minusA r bytes (challenge r a msg) =
        bodySuffix shared doubleBase compress (challenge r a msg) minusA r bytes := by
      unfold prehashed bodySuffix scalarSuffix
      rw [hfalse]
      rfl
    refine ⟨after, ?_⟩
    rw [hentry, hfalse, hspec]
    exact hbody


/-- Only the concrete Dalek entry memory and its initialized globals.
The cached minus-A payload relation is kept explicit until the constructor's
radix-51 negation is connected to the chosen mathematical point layout. -/
structure EntryMemory (g : Globals) (cg : Challenge.Globals)
    (layout : Layout Point Scalar Result) (initial : GlobalState)
    (key signature message : Pointer) (a r bytes : Bytes32) (minusA : Point)
    (msg : List (BitVec 8)) : Prop where
  wellFormed : initial.WF
  keyRange : SmallRange initial.mem key 192
  signatureRange : SmallRange initial.mem signature 64
  messageRange : SmallRange initial.mem message msg.length
  publicKey : initial.mem.readAt key 256 = a
  signatureR : initial.mem.readAt signature 256 = r
  signatureS : initial.mem.readAt (signature.add 32#64) 256 = bytes
  point : ReadBytes initial (key.add 32#64) 160 (layout.point minusA)
  messageBytes : ∀ (i : Nat) (hi : i < msg.length),
    initial.mem.readAt (message.add (BitVec.ofNat 64 i)) 8 = msg[i]
  lengthBound : msg.length < 2 ^ 63
  identity : ReadBytes initial g.address0 40 (1#320)
  cache : SmallRange initial.mem g.address1 1
  keyCache : (Range.of (key.add 32#64) 1280).Disjoint (Range.of g.address1 8)
  signatureCache : (Range.of signature 256).Disjoint (Range.of g.address1 8)
  shaIV : ReadBytes initial cg.address0 64 Challenge.initialWords

/-- Fuel-independent execution and actual callee-frame cleanup, from exact
challenge execution plus the remaining individually named primitive contracts. -/
theorem program_call_of_leaf_contracts {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (contracts : LeafContracts p g layout shared doubleBase compress)
    (cp : Challenge.Primitives) (cg : Challenge.Globals) (sha : Challenge.Sha512Model)
    (hlink : p.challengeScalar = (Challenge.program cp cg).call)
    (hcompress : Challenge.CompressContract cp.sha512Compress sha)
    (hscalar : Challenge.ScalarFromSha512Contract cp.scalarFromSha512 sha)
    (hencoding : ∀ r a msg, layout.scalar (challenge r a msg) =
      Challenge.digestScalarBytes (sha.digest (Challenge.transcript r a msg)))
    (hidentity : layout.identity = identityBytes)
    (initial : GlobalState) (key signature message : Pointer)
    (a r bytes : Bytes32) (minusA : Point) (msg : List (BitVec 8))
    (hm : EntryMemory g cg layout initial key signature message a r bytes minusA msg) :
    ∃ after, (program p g).call (inputArgs key signature message msg.length) initial =
      .value (.cons (.value (code (prehashed shared doubleBase compress minusA r bytes
        (challenge r a msg)))) .nil, after) := by
  obtain ⟨after, hrun⟩ := program_from_entry_of_leaf_contracts p g layout shared doubleBase
    compress challenge contracts cp cg sha hlink hcompress hscalar hencoding hidentity
    (Env.init (inputArgs key signature message msg.length).get) initial key signature message
    a r bytes minusA msg rfl rfl rfl rfl hm.wellFormed hm.keyRange hm.signatureRange
    hm.messageRange hm.publicKey hm.signatureR hm.signatureS hm.point hm.messageBytes
    hm.lengthBound hm.identity hm.cache hm.keyCache hm.signatureCache hm.shaIV
  have hr : (program p g).run (inputArgs key signature message msg.length) initial =
      .value (.cons (.value (code (prehashed shared doubleBase compress minusA r bytes
        (challenge r a msg)))) .nil, after) := by
    rw [Func.run_runFrom_eq]
    exact hrun
  exact ⟨_, Func.call_of_run hr⟩

end Agave.Ed25519.Verifier.Execution.Dalek

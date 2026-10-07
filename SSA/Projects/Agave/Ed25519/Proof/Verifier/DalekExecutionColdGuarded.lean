import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionColdUnder

/-! Backend readiness is only used after the public-key small-order check
continues to R decoding. Early rejection has no decoder-prefix obligation. -/
namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

theorem program_from_entry_of_leaf_contracts_cold_guarded {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (serialReady avx2Ready : BackendReadyPredicate)
    (contracts : NonDecoderLeafContractsUnder p g serialReady avx2Ready layout shared doubleBase compress)
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
    (hdecode : DecompressContractUnder (Encoding.Decompress.Execution.Ready ddg dsg)
      p.decompress layout shared)
    (cp : Challenge.Primitives) (cg : Challenge.Globals)
    (sg : ScalarWide.Globals) (scg : SHA512Finalization.CompressionGlobals)
    (compression : Agave.Ed25519.SHA512.Compression)
    (hlink : p.challengeScalar = (Challenge.program cp cg).call)
    (hcompress : SHA512Finalization.CompressContractUnder scg cp.sha512Compress compression)
    (hscalar : SHA512Finalization.ScalarFromSha512ColdContract scg sg cp.scalarFromSha512 compression)
    (hencoding : ∀ r a msg, layout.scalar (challenge r a msg) =
      Challenge.digestScalarBytes (Agave.Ed25519.SHA512.digest compression (Challenge.transcript r a msg)))
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
    (hiv : ReadBytes initial cg.address0 64 Challenge.initialWords)
    (hready : ColdEntryReady scg sg g ddg dsg initial key signature message)
    (hdecoderReady : Encoding.Decompress.Execution.Ready ddg dsg initial)
    (hbackend : shared.smallOrder minusA = false → ColdBackendsReady p serialReady avx2Ready scg g initial key signature message msg.length bytes) :
    ∃ after, (program p g).runFrom E 0 initial =
      .value (.cons (.value (code (prehashed shared doubleBase compress minusA r bytes
        (challenge r a msg)))) .nil, after) := by
  obtain ⟨challenged, multiplied, compared, htrace, hc, hchallenge, hm, he, hentry⟩ :=
    entry_of_sha_contracts_cold_trace p g layout shared challenge cp cg sg scg compression ddg dsg hlink hcompress hscalar
      hencoding contracts.pointMulByPow2
      contracts.pointConstantTimeEq hidentity E initial key signature message a r minusA msg
      hkeyE hsigE hmsgE hlenE hwf hk hsig hmsg ha hr hA hmbytes hmlen hglobal hiv hready
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
    have hmemory := cold_entry_body_memory scg initial challenged multiplied compared hwf key signature g
      layout (challenge r a msg) minusA r bytes hc hchallenge hm he hA hsig hrbytes hsbytes hglobal hcache
      (hready.stackCache hwf) hready.keyCache hready.signatureCache hready.identityCache hready.dalekCache
    have hdisjoint := entry_body_disjoint initial hwf key signature g hA.1 hsig hglobal.1
      hcache hkeyCache hsigCache
    obtain ⟨after, hbody⟩ := body_of_contextual_contracts p g layout shared doubleBase compress
      serialReady avx2Ready contracts (Encoding.Decompress.Execution.Ready ddg dsg) hdecode hidentity
      (entryTailPointers initial key signature g) (entryPointPointers initial g)
      (stackSlot initial 0) rfl (entryEnv E g initial key false) compared (challenge r a msg)
      minusA r bytes hregs hmemory hdisjoint
      (cold_entry_decoder_ready scg ddg dsg initial challenged multiplied compared hwf hc hm he
        hdecoderReady (hready.stackCache hwf 3) hready.curveDCache hready.sqrtM1Cache)
      (hbackend hfalse challenged multiplied compared htrace hc hm he)
    have hspec : prehashed shared doubleBase compress minusA r bytes (challenge r a msg) =
        bodySuffix shared doubleBase compress (challenge r a msg) minusA r bytes := by
      unfold prehashed bodySuffix scalarSuffix
      rw [hfalse]
      rfl
    refine ⟨after, ?_⟩
    rw [hentry, hfalse, hspec]
    exact hbody


/-- Fuel-independent execution and actual callee-frame cleanup, from exact
challenge execution plus the remaining individually named primitive contracts. -/
theorem program_call_of_leaf_contracts_cold_guarded {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (serialReady avx2Ready : BackendReadyPredicate)
    (contracts : NonDecoderLeafContractsUnder p g serialReady avx2Ready layout shared doubleBase compress)
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
    (hdecode : DecompressContractUnder (Encoding.Decompress.Execution.Ready ddg dsg)
      p.decompress layout shared)
    (cp : Challenge.Primitives) (cg : Challenge.Globals)
    (sg : ScalarWide.Globals) (scg : SHA512Finalization.CompressionGlobals)
    (compression : Agave.Ed25519.SHA512.Compression)
    (hlink : p.challengeScalar = (Challenge.program cp cg).call)
    (hcompress : SHA512Finalization.CompressContractUnder scg cp.sha512Compress compression)
    (hscalar : SHA512Finalization.ScalarFromSha512ColdContract scg sg cp.scalarFromSha512 compression)
    (hencoding : ∀ r a msg, layout.scalar (challenge r a msg) =
      Challenge.digestScalarBytes (Agave.Ed25519.SHA512.digest compression (Challenge.transcript r a msg)))
    (hidentity : layout.identity = identityBytes)
    (initial : GlobalState) (key signature message : Pointer)
    (a r bytes : Bytes32) (minusA : Point) (msg : List (BitVec 8))
    (hm : EntryMemory g cg layout initial key signature message a r bytes minusA msg)
    (hready : ColdEntryReady scg sg g ddg dsg initial key signature message)
    (hdecoderReady : Encoding.Decompress.Execution.Ready ddg dsg initial)
    (hbackend : shared.smallOrder minusA = false → ColdBackendsReady p serialReady avx2Ready scg g initial key signature message msg.length bytes) :
    ∃ after, (program p g).call (inputArgs key signature message msg.length) initial =
      .value (.cons (.value (code (prehashed shared doubleBase compress minusA r bytes
        (challenge r a msg)))) .nil, after) := by
  obtain ⟨after, hrun⟩ := program_from_entry_of_leaf_contracts_cold_guarded p g layout shared doubleBase
    compress challenge serialReady avx2Ready contracts ddg dsg hdecode cp cg sg scg compression hlink hcompress hscalar hencoding hidentity
    (Env.init (inputArgs key signature message msg.length).get) initial key signature message
    a r bytes minusA msg rfl rfl rfl rfl hm.wellFormed hm.keyRange hm.signatureRange
    hm.messageRange hm.publicKey hm.signatureR hm.signatureS hm.point hm.messageBytes
    hm.lengthBound hm.identity hm.cache hm.keyCache hm.signatureCache hm.shaIV hready hdecoderReady hbackend
  have hr : (program p g).run (inputArgs key signature message msg.length) initial =
      .value (.cons (.value (code (prehashed shared doubleBase compress minusA r bytes
        (challenge r a msg)))) .nil, after) := by
    rw [Func.run_runFrom_eq]
    exact hrun
  exact ⟨_, Func.call_of_run hr⟩

end Agave.Ed25519.Verifier.Execution.Dalek

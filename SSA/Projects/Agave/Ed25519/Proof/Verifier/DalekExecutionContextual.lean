import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionLinked
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekChallengeContextual
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionDecoderContextual

/-! The existing body proof is unchanged. Only entry composition is specialized
to the invocation-local finalizer readiness and the contextual challenge call. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

/-- Both decoder constants are ordinary caller reads. The exact entry frames
transport them past challenge/cofactor calls, the identity stores and equality
without any universal global-availability assumption. -/
theorem entry_decoder_ready
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
    (initial challenged multiplied compared : GlobalState) (hwf : initial.WF)
    (hc : OutputFrame (allocated initial) challenged (stackSlot initial 12) 32)
    (hm : OutputFrame challenged multiplied (stackSlot initial 4) 160)
    (he : ReadOnlyFrame (identityStoreState multiplied (stackSlot initial 3)) compared)
    (hready : Encoding.Decompress.Execution.Ready ddg dsg initial) :
    Encoding.Decompress.Execution.Ready ddg dsg compared := by
  have hid : SmallRange multiplied.mem (stackSlot initial 3) 160 :=
    hm.live _ _ (hc.live _ _ (stackSlot_live initial hwf 3 13 (by decide)))
  have hcaller {ptr : Pointer} {n : Nat} {value : BitVec (8 * n)}
      (hv : ReadBytes initial ptr n value) : ReadBytes compared ptr n value := by
    apply entry_readBytes initial challenged multiplied compared hc hm he hid ptr n value
      (stackState_readBytes initial hwf 13 hv)
    · exact (stackSlot_disjoint_caller initial hwf 12 hv.1 256 (8 * n)).symm
    · exact (stackSlot_disjoint_caller initial hwf 4 hv.1 1280 (8 * n)).symm
    · exact (stackSlot_disjoint_caller initial hwf 3 hv.1 1280 (8 * n)).symm
  exact ⟨hcaller hready.curveD, hcaller hready.sqrtM1⟩

theorem program_from_entry_of_leaf_contracts_under {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (contracts : NonDecoderLeafContracts p g layout shared doubleBase compress)
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
    (hdecode : DecompressContractUnder (Encoding.Decompress.Execution.Ready ddg dsg)
      p.decompress layout shared)
    (cp : Challenge.Primitives) (cg : Challenge.Globals) (sha : Challenge.Sha512Model)
    (sg : ScalarWide.Globals)
    (hlink : p.challengeScalar = (Challenge.program cp cg).call)
    (hcompress : Challenge.CompressContract cp.sha512Compress sha)
    (hscalar : SHA512Finalization.ScalarFromSha512ContractUnder
      (ScalarWide.Ready sg) cp.scalarFromSha512 sha)
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
    (hiv : ReadBytes initial cg.address0 64 Challenge.initialWords)
    (hready : ScalarWide.Ready sg (allocated initial) (stackSlot initial 12))
    (hdecoderReady : Encoding.Decompress.Execution.Ready ddg dsg initial) :
    ∃ after, (program p g).runFrom E 0 initial =
      .value (.cons (.value (code (prehashed shared doubleBase compress minusA r bytes
        (challenge r a msg)))) .nil, after) := by
  obtain ⟨challenged, multiplied, compared, hc, hchallenge, hm, he, hentry⟩ :=
    entry_of_sha_contracts_under p g layout shared challenge cp cg sha sg hlink hcompress hscalar
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
    have hmemory := entry_body_memory initial challenged multiplied compared hwf key signature g
      layout (challenge r a msg) minusA r bytes hc hchallenge hm he hA hsig hrbytes hsbytes hglobal hcache
    have hdisjoint := entry_body_disjoint initial hwf key signature g hA.1 hsig hglobal.1
      hcache hkeyCache hsigCache
    obtain ⟨after, hbody⟩ := body_of_decoder_contract_under p g layout shared doubleBase compress
      contracts (Encoding.Decompress.Execution.Ready ddg dsg) hdecode hidentity
      (entryTailPointers initial key signature g) (entryPointPointers initial g)
      (stackSlot initial 0) rfl (entryEnv E g initial key false) compared (challenge r a msg)
      minusA r bytes hregs hmemory hdisjoint
      (entry_decoder_ready ddg dsg initial challenged multiplied compared hwf hc hm he hdecoderReady)
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
theorem program_call_of_leaf_contracts_under {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (contracts : NonDecoderLeafContracts p g layout shared doubleBase compress)
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
    (hdecode : DecompressContractUnder (Encoding.Decompress.Execution.Ready ddg dsg)
      p.decompress layout shared)
    (cp : Challenge.Primitives) (cg : Challenge.Globals) (sha : Challenge.Sha512Model)
    (sg : ScalarWide.Globals)
    (hlink : p.challengeScalar = (Challenge.program cp cg).call)
    (hcompress : Challenge.CompressContract cp.sha512Compress sha)
    (hscalar : SHA512Finalization.ScalarFromSha512ContractUnder
      (ScalarWide.Ready sg) cp.scalarFromSha512 sha)
    (hencoding : ∀ r a msg, layout.scalar (challenge r a msg) =
      Challenge.digestScalarBytes (sha.digest (Challenge.transcript r a msg)))
    (hidentity : layout.identity = identityBytes)
    (initial : GlobalState) (key signature message : Pointer)
    (a r bytes : Bytes32) (minusA : Point) (msg : List (BitVec 8))
    (hm : EntryMemory g cg layout initial key signature message a r bytes minusA msg)
    (hready : ScalarWide.Ready sg (allocated initial) (stackSlot initial 12))
    (hdecoderReady : Encoding.Decompress.Execution.Ready ddg dsg initial) :
    ∃ after, (program p g).call (inputArgs key signature message msg.length) initial =
      .value (.cons (.value (code (prehashed shared doubleBase compress minusA r bytes
        (challenge r a msg)))) .nil, after) := by
  obtain ⟨after, hrun⟩ := program_from_entry_of_leaf_contracts_under p g layout shared doubleBase
    compress challenge contracts ddg dsg hdecode cp cg sha sg hlink hcompress hscalar hencoding hidentity
    (Env.init (inputArgs key signature message msg.length).get) initial key signature message
    a r bytes minusA msg rfl rfl rfl rfl hm.wellFormed hm.keyRange hm.signatureRange
    hm.messageRange hm.publicKey hm.signatureR hm.signatureS hm.point hm.messageBytes
    hm.lengthBound hm.identity hm.cache hm.keyCache hm.signatureCache hm.shaIV hready hdecoderReady
  have hr : (program p g).run (inputArgs key signature message msg.length) initial =
      .value (.cons (.value (code (prehashed shared doubleBase compress minusA r bytes
        (challenge r a msg)))) .nil, after) := by
    rw [Func.run_runFrom_eq]
    exact hrun
  exact ⟨_, Func.call_of_run hr⟩

end Agave.Ed25519.Verifier.Execution.Dalek

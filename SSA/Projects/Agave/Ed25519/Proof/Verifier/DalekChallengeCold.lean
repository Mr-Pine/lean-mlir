import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekColdReady

/-! Actual challenge execution with a cold or warm SHA dispatch cache.
Only the designated cache allocation and challenge output can change. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge

theorem challenge_call_of_sha_contracts_cold
    (scg : SHA512Finalization.CompressionGlobals) (sg : ScalarWide.Globals)
    (cp : Challenge.Primitives) (cg : Challenge.Globals)
    (compression : Agave.Ed25519.SHA512.Compression)
    (hcompress : SHA512Finalization.CompressContractUnder scg cp.sha512Compress compression)
    (hscalar : SHA512Finalization.ScalarFromSha512ColdContract scg sg cp.scalarFromSha512 compression)
    (layout : Layout Point Scalar Result)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (hencoding : ∀ r a msg, layout.scalar (challenge r a msg) =
      Challenge.digestScalarBytes (Agave.Ed25519.SHA512.digest compression (Challenge.transcript r a msg)))
    (out key signature message : Pointer) (state : GlobalState)
    (a r : Bytes32) (msg : List (BitVec 8)) (hwf : state.WF)
    (hready : Challenge.ColdChallengeReady scg sg state out key signature message)
    (hout : SmallRange state.mem out 32)
    (hkey : SmallRange state.mem key 192) (hsig : SmallRange state.mem signature 64)
    (hmessage : SmallRange state.mem message msg.length)
    (ha : state.mem.readAt key 256 = a) (hr : state.mem.readAt signature 256 = r)
    (hread : ∀ (i : Nat) (hi : i < msg.length),
      state.mem.readAt (message.add (BitVec.ofNat 64 i)) 8 = msg[i])
    (hlen : msg.length < 2 ^ 63)
    (hiv : ReadBytes state cg.address0 64 Challenge.initialWords)
    (hdk : (Range.of out 256).Disjoint (Range.of key 1536))
    (hds : (Range.of out 256).Disjoint (Range.of signature 512))
    (hdm : (Range.of out 256).Disjoint (Range.of message (8 * msg.length))) :
    ∃ after,
      (Challenge.program cp cg).call
        (Challenge.challengeArgs out key signature message (BitVec.ofNat 64 msg.length))
        state = .value (.nil, after) ∧
      SHA512Finalization.CacheOutputEffect scg state after out (layout.scalar (challenge r a msg)) ∧
      SHA512Finalization.CacheAwareOutputFrame scg state after out 32 ∧
      ReadBytes after out 32 (layout.scalar (challenge r a msg)) := by
  have hlen64 : msg.length < 2 ^ 64 := by omega
  have hn : (BitVec.ofNat 64 msg.length).toNat = msg.length := Nat.mod_eq_of_lt hlen64
  obtain ⟨after, hcall, heffect, _, houtput, hw⟩ :=
    Challenge.challenge_call_cold scg sg cp cg compression hcompress hscalar
      state out key signature message (BitVec.ofNat 64 msg.length) r a msg hwf hready
      hout hkey hsig (by simpa only [hn] using hmessage) ha hr
      (by simpa only [hn] using challenge_readBytes_of_getElem state message msg hread)
      hiv.1 hiv.2 hdk hds (by simpa only [hn] using hdm)
  rw [← hencoding] at heffect houtput
  exact ⟨after, hcall, heffect, heffect.callerFrame hwf hready.compression hready.outputCache,
    heffect.smallRange out 32 hready.outputCache hout, houtput⟩

/-- Warm-cache exact memory preservation is a consequence of the cold-capable
frame and the actual dispatch transition; no universal warm-cache assumption
or separate whole-run equality is needed. -/
theorem cold_challenge_warm_outputFrame
    (scg : SHA512Finalization.CompressionGlobals) (before after : GlobalState)
    (out : Pointer) (scalar : Bytes32)
    (hready : SHA512Finalization.CompressionReady scg before)
    (hout : out.id ≠ scg.cache) (hwarm : SHA512Finalization.CacheWarm scg before)
    (heffect : SHA512Finalization.CacheOutputEffect scg before after out scalar)
    (hwf : after.WF) : OutputFrame before after out 32 :=
  challenge_outputFrame_of_store before after out scalar
    (heffect.warm hready hout hwarm).memory hwf

/-- The actual cold-capable challenge theorem specializes to exact output-only
memory behavior whenever this invocation begins with a populated SHA cache. -/
theorem challenge_call_of_sha_contracts_cold_warm
    (scg : SHA512Finalization.CompressionGlobals) (sg : ScalarWide.Globals)
    (cp : Challenge.Primitives) (cg : Challenge.Globals)
    (compression : Agave.Ed25519.SHA512.Compression)
    (hcompress : SHA512Finalization.CompressContractUnder scg cp.sha512Compress compression)
    (hscalar : SHA512Finalization.ScalarFromSha512ColdContract scg sg cp.scalarFromSha512 compression)
    (layout : Layout Point Scalar Result)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (hencoding : ∀ r a msg, layout.scalar (challenge r a msg) =
      Challenge.digestScalarBytes (Agave.Ed25519.SHA512.digest compression (Challenge.transcript r a msg)))
    (out key signature message : Pointer) (state : GlobalState)
    (a r : Bytes32) (msg : List (BitVec 8)) (hwf : state.WF)
    (hready : Challenge.ColdChallengeReady scg sg state out key signature message)
    (hwarm : SHA512Finalization.CacheWarm scg state)
    (hout : SmallRange state.mem out 32)
    (hkey : SmallRange state.mem key 192) (hsig : SmallRange state.mem signature 64)
    (hmessage : SmallRange state.mem message msg.length)
    (ha : state.mem.readAt key 256 = a) (hr : state.mem.readAt signature 256 = r)
    (hread : ∀ (i : Nat) (hi : i < msg.length),
      state.mem.readAt (message.add (BitVec.ofNat 64 i)) 8 = msg[i])
    (hlen : msg.length < 2 ^ 63)
    (hiv : ReadBytes state cg.address0 64 Challenge.initialWords)
    (hdk : (Range.of out 256).Disjoint (Range.of key 1536))
    (hds : (Range.of out 256).Disjoint (Range.of signature 512))
    (hdm : (Range.of out 256).Disjoint (Range.of message (8 * msg.length))) :
    ∃ after,
      (Challenge.program cp cg).call
        (Challenge.challengeArgs out key signature message (BitVec.ofNat 64 msg.length))
        state = .value (.nil, after) ∧
      Challenge.StoreEffect state after out (layout.scalar (challenge r a msg)) ∧
      OutputFrame state after out 32 ∧
      ReadBytes after out 32 (layout.scalar (challenge r a msg)) := by
  obtain ⟨after, hcall, heffect, hframe, hreadback⟩ :=
    challenge_call_of_sha_contracts_cold scg sg cp cg compression hcompress hscalar
      layout challenge hencoding out key signature message state a r msg hwf hready
      hout hkey hsig hmessage ha hr hread hlen hiv hdk hds hdm
  exact ⟨after, hcall, heffect.warm hready.compression hready.outputCache hwarm,
    cold_challenge_warm_outputFrame scg state after out _ hready.compression
      hready.outputCache hwarm heffect hframe.wellFormed, hreadback⟩

/-- Entry execution with the actual extracted challenge call and only a
per-invocation initialized-IV premise. In particular this theorem requires no
universally quantified `ChallengeIVAvailable` or `ChallengeContract` premise. -/
theorem entry_of_sha_contracts_cold {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (shared : Shared Point Scalar)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (cp : Challenge.Primitives) (cg : Challenge.Globals)
    (sg : ScalarWide.Globals) (scg : SHA512Finalization.CompressionGlobals)
    (compression : Agave.Ed25519.SHA512.Compression)
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
    (hlink : p.challengeScalar = (Challenge.program cp cg).call)
    (hcompress : SHA512Finalization.CompressContractUnder scg cp.sha512Compress compression)
    (hscalar : SHA512Finalization.ScalarFromSha512ColdContract scg sg cp.scalarFromSha512 compression)
    (hencoding : ∀ r a msg, layout.scalar (challenge r a msg) =
      Challenge.digestScalarBytes (Agave.Ed25519.SHA512.digest compression (Challenge.transcript r a msg)))
    (hmul : CofactorContract p.pointMulByPow2 layout)
    (heq : SmallOrderEqContract p.pointConstantTimeEq layout shared)
    (hidLayout : layout.identity = identityBytes)
    (E : Env program.Γ) (initial : GlobalState) (key signature message : Pointer)
    (a r : Bytes32) (A : Point) (msg : List (BitVec 8))
    (hkeyE : E.read (%arg0) = .value key)
    (hsigE : E.read (%arg1) = .value signature)
    (hmsgE : E.read (%arg2) = .value message)
    (hlenE : E.read (%arg3) = .value (BitVec.ofNat 64 msg.length))
    (hwf : initial.WF) (hk : SmallRange initial.mem key 192)
    (hsig : SmallRange initial.mem signature 64)
    (hmsg : SmallRange initial.mem message msg.length)
    (ha : initial.mem.readAt key 256 = a)
    (hr : initial.mem.readAt signature 256 = r)
    (hA : ReadBytes initial (key.add 32) 160 (layout.point A))
    (hmbytes : ∀ (i : Nat) (hi : i < msg.length),
      initial.mem.readAt (message.add (BitVec.ofNat 64 i)) 8 = msg[i])
    (hmlen : msg.length < 2^63)
    (hglobal : ReadBytes initial g.address0 40 (1#320))
    (hiv : ReadBytes initial cg.address0 64 Challenge.initialWords)
    (hready : ColdEntryReady scg sg g ddg dsg initial key signature message) :
    ∃ challenged multiplied compared,
      SHA512Finalization.CacheAwareOutputFrame scg (allocated initial) challenged (stackSlot initial 12) 32 ∧
      ReadBytes challenged (stackSlot initial 12) 32 (layout.scalar (challenge r a msg)) ∧
      OutputFrame challenged multiplied (stackSlot initial 4) 160 ∧
      ReadOnlyFrame (identityStoreState multiplied (stackSlot initial 3)) compared ∧
      (program p g).runFrom E 0 initial =
        if shared.smallOrder A then
          (program p g).runFrom ((entryEnv E g initial key (shared.smallOrder A))[%71 := .value 2]) 13 compared
        else (program p g).runFrom (entryEnv E g initial key (shared.smallOrder A)) 1 compared := by
  have hwf0 : (allocated initial).WF := stackState_wf initial hwf 13
  have hk0 := stackState_live initial hwf 13 hk
  have hs0 := stackState_live initial hwf 13 hsig
  have hm0 := stackState_live initial hwf 13 hmsg
  have hA0 := stackState_readBytes initial hwf 13 hA
  have hg0 := stackState_readBytes initial hwf 13 hglobal
  have hstack (i : Nat) (hi : i < 13) := stackSlot_live initial hwf i 13 hi
  have hbytes : ∀ (i : Nat) (hi : i < msg.length),
      (allocated initial).mem.readAt (message.add (BitVec.ofNat 64 i)) 8 = msg[i] := by
    intro i hi
    exact (stackState_read initial hwf 13
      (smallRange_add hmsg (k := i) (count := 1) (by omega)) 8).trans (hmbytes i hi)
  have hiv0 := stackState_readBytes initial hwf 13 hiv
  obtain ⟨challenged, hccall, hstore, hc, hchallengeRead⟩ :=
    challenge_call_of_sha_contracts_cold scg sg cp cg compression hcompress hscalar
      layout challenge hencoding (stackSlot initial 12) key signature message (allocated initial)
      a r msg hwf0 (hready.challenge hwf) (hstack 12 (by decide)) hk0 hs0 hm0
      ((stackState_read initial hwf 13 hk 256).trans ha)
      ((stackState_read initial hwf 13 hsig 256).trans hr) hbytes hmlen hiv0
      (stackSlot_disjoint_caller initial hwf 12 hk 256 1536)
      (stackSlot_disjoint_caller initial hwf 12 hsig 256 512)
      (stackSlot_disjoint_caller initial hwf 12 hmsg 256 (8 * msg.length))
  rw [← hlink] at hccall
  have hAc : ReadBytes challenged (key.add 32) 160 (layout.point A) :=
    hc.readBytes _ _ _ hA0 (by simpa using hready.keyCache)
      (stackSlot_disjoint_caller initial hwf 12 hA.1 256 1280).symm
  have hgc : ReadBytes challenged g.address0 40 (1#320) :=
    hc.readBytes _ _ _ hg0 hready.identityCache
      (stackSlot_disjoint_caller initial hwf 12 hglobal.1 256 320).symm
  obtain ⟨multiplied, hmcall, hm, hcofactor⟩ := hmul (stackSlot initial 4) (key.add 32)
    challenged A hc.wellFormed (hc.live _ _ (hready.stackCache hwf 4) (hstack 4 (by decide))) hAc
    (stackSlot_disjoint_caller initial hwf 4 hA.1 1280 1280)
  have hid : SmallRange multiplied.mem (stackSlot initial 3) 160 :=
    hm.live _ _ (hc.live _ _ (hready.stackCache hwf 3) (hstack 3 (by decide)))
  have hgm : ReadBytes multiplied g.address0 40 (1#320) :=
    hm.readBytes _ _ _ _ _ _ _ hgc
      (stackSlot_disjoint_caller initial hwf 4 hglobal.1 1280 320).symm
  have hiFrame := identity_frame multiplied (stackSlot initial 3) hm.wellFormed hid
  have hcofactor' := hiFrame.readBytes _ _ _ _ _ _ _ hcofactor
    (stackSlot_disjoint initial 4 3 (by decide) 1280 1280)
  have hidentity : ReadBytes (identityStoreState multiplied (stackSlot initial 3))
      (stackSlot initial 3) 160 layout.identity := by
    rw [hidLayout]
    exact identity_readback multiplied (stackSlot initial 3) hid
  obtain ⟨compared, hecall, he⟩ := heq (stackSlot initial 4) (stackSlot initial 3)
    (identityStoreState multiplied (stackSlot initial 3)) A hiFrame.wellFormed
    hcofactor' hidentity
  refine ⟨challenged, multiplied, compared, hc, hchallengeRead, hm, he, ?_⟩
  exact entry_block p g E initial challenged multiplied compared key signature message
    (BitVec.ofNat 64 msg.length) (shared.smallOrder A) hkeyE hsigE hmsgE hlenE hccall
    (hc.live _ _ hready.keyCache hk0) hmcall hid hgm
    (stackSlot_disjoint_caller initial hwf 3 hglobal.1 1280 320).symm hecall


end Agave.Ed25519.Verifier.Execution.Dalek

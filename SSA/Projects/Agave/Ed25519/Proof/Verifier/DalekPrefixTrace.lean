import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekChallengeCold
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionDecoderContextual

/-! Exact primitive-call traces for the verifier prefix. Frames alone cannot
preserve the lengths of immutable global allocations: a zero-extension is
observationally read-only. These traces restrict readiness to states actually
returned by the deterministic linked callees. No execution premise is added. -/
namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

/-- Actual four-call scalar-check sequence, without a semantic result premise. -/
def ScalarCallTrace (p : Primitives) (signature scratch : Pointer)
    (before after : GlobalState) : Prop :=
  let high := choiceByte ((255#8).slt (before.mem.readAt (signature.add 63#64) 8))
  ∃ (first reduced equal : GlobalState) (equalValue : BitVec 8),
    p.blackBoxByte (.cons (.value high) .nil) before = .value (.cons (.value high) .nil, first) ∧
    p.scalarReduce (args2 scratch (signature.add 32#64)) first = .value (.nil, reduced) ∧
    p.bytesConstantTimeEq (args2 (signature.add 32#64) scratch) reduced =
      .value (.cons (.value equalValue) .nil, equal) ∧
    p.blackBoxByte (.cons (.value (equalValue &&& high)) .nil) equal =
      .value (.cons (.value (equalValue &&& high)) .nil, after)

/-- Actual cofactor and equality calls surrounding the explicit copies/stores. -/
def PointCallTrace (p : Primitives) (q : PointPointers) (before after : GlobalState) : Prop :=
  ∃ (middle : GlobalState) (returned : BitVec 8),
    p.pointMulByPow2 (.cons (.value q.cofactor) (.cons (.value q.point)
      (.cons (.value 3#32) .nil))) (optionCopyState before q.option q.slot29 q.slot30 q.point) =
      .value (.nil, middle) ∧
    p.pointConstantTimeEq (args2 q.cofactor q.identity) (identityStoreState middle q.identity) =
      .value (.cons (.value returned) .nil, after)

/-- Actual challenge, cofactor, and equality calls in block zero. -/
def ColdCallTrace (p : Primitives) (initial : GlobalState)
    (key signature message : Pointer) (length : Nat)
    (challenged multiplied compared : GlobalState) : Prop :=
  p.challengeScalar (.cons (.value (stackSlot initial 12)) (.cons (.value key)
    (.cons (.value signature) (.cons (.value message)
      (.cons (.value (BitVec.ofNat 64 length)) .nil))))) (allocated initial) =
      .value (.nil, challenged) ∧
  p.pointMulByPow2 (.cons (.value (stackSlot initial 4)) (.cons (.value (key.add 32#64))
    (.cons (.value 3#32) .nil))) challenged = .value (.nil, multiplied) ∧
  ∃ returned : BitVec 8,
    p.pointConstantTimeEq (args2 (stackSlot initial 4) (stackSlot initial 3))
      (identityStoreState multiplied (stackSlot initial 3)) =
        .value (.cons (.value returned) .nil, compared)

set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

theorem scalar_check_of_contracts_trace {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (hreduce : ScalarReduceContract p.scalarReduce layout)
    (hequal : BytesEqContract p.bytesConstantTimeEq)
    (hblack : BlackBoxContract p.blackBoxByte)
    (E : Env program.Γ) (state : GlobalState) (signature scratch : Pointer)
    (bytes : Bytes32)
    (hsig : E.read (%arg1) = .value signature)
    (hscratch : E.read (%20) = .value scratch)
    (h32 : E.read (%1) = .value 32#64)
    (h63 : E.read (%12) = .value 63#64)
    (hminus : E.read (%13) = .value 255#8)
    (hone : E.read (%14) = .value 1#8)
    (hwf : state.WF) (hsigfit : SmallRange state.mem signature 64)
    (hfit : SmallRange state.mem scratch 32)
    (hbytes : ReadBytes state (signature.add 32#64) 32 bytes)
    (hd : (Range.of scratch 256).Disjoint (Range.of (signature.add 32#64) 256)) :
    ∃ after, ScalarCallTrace p signature scratch state after ∧ OutputFrame state after scratch 32 ∧
      (program p g).runFrom E 4 state =
        (program p g).runFrom
          (scalarBlockEnv E signature (bytes.extractLsb' 0 8) (bytes.extractLsb' 248 8)
            (decide (bytes = layout.reduce bytes)))
          (if scalarGate layout bytes then 5 else 11) after := by
  obtain ⟨blackFirst, hbf, hbfFrame⟩ := hblack
    (choiceByte ((255#8).slt (bytes.extractLsb' 248 8))) state hwf
  have hbytesFirst := ReadOnlyFrame.readBytes state blackFirst
    (signature.add 32#64) 32 bytes hbfFrame hbytes
  obtain ⟨middle, hrcall, hframe, hred⟩ := hreduce scratch (signature.add 32#64)
    blackFirst bytes hbfFrame.wellFormed (hbfFrame.live _ _ hfit) hbytesFirst hd
  have hb := OutputFrame.readBytes blackFirst middle scratch
    (signature.add 32#64) 32 32 bytes hframe hbytesFirst hd.symm
  obtain ⟨equalAfter, hecall, hro⟩ := hequal (signature.add 32#64) scratch middle bytes
    (layout.reduce bytes) hframe.wellFormed hb hred
  have hfirst := scalar_signature_subread state signature bytes hbytes 0 1 (by decide)
  have hlast := scalar_signature_subread state signature bytes hbytes 31 1 (by decide)
  change state.mem.readAt (signature.add 32#64) 8 = bytes.extractLsb' 0 8 at hfirst
  change state.mem.readAt (signature.add 63#64) 8 = bytes.extractLsb' 248 8 at hlast
  have hecall' : p.bytesConstantTimeEq (args2 (signature.add 32#64) scratch) middle =
    .value (.cons (.value (choiceByte (decide (bytes = layout.reduce bytes)))) .nil, equalAfter) := by
    simpa only [choiceByte, decide_eq_true_eq] using hecall
  have hsame : decide (bytes = layout.reduce bytes) = decide (layout.reduce bytes = bytes) := by
    simp only [eq_comm]
  have hgate : (decide (bytes = layout.reduce bytes) && (255#8).slt (bytes.extractLsb' 248 8)) =
      scalarGate layout bytes := by
    unfold scalarGate scalarHighBitClear
    have hnegative : (-1 : BitVec 8) = 255#8 := by decide
    rw [hsame, Bool.and_comm, hnegative]
  obtain ⟨after, hbl, hblFrame⟩ := hblack
    (choiceByte (decide (bytes = layout.reduce bytes) &&
      (255#8).slt (bytes.extractLsb' 248 8))) equalAfter hro.wellFormed
  have htrace : ScalarCallTrace p signature scratch state after := by
    refine ⟨blackFirst, middle, equalAfter, _, ?_, hrcall, hecall', ?_⟩
    · simpa only [hlast] using hbf
    · simpa only [hlast, choiceByte_and] using hbl
  refine ⟨after, htrace, hbfFrame.thenOutput ((hframe.thenReadOnly hro).thenReadOnly hblFrame), ?_⟩
  rw [scalar_check_block p g E state blackFirst middle equalAfter after signature scratch
    (bytes.extractLsb' 0 8) (bytes.extractLsb' 248 8) (decide (bytes = layout.reduce bytes))
    hsig hscratch h32 h63 hminus hone hsigfit hfirst hlast hbf hbl hrcall hecall', hgate]

theorem point_check_of_contracts_trace {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (shared : Shared Point Scalar)
    (hidentity : layout.identity = identityBytes)
    (hmul : CofactorContract p.pointMulByPow2 layout)
    (hequal : SmallOrderEqContract p.pointConstantTimeEq layout shared)
    (q : PointPointers) (E : Env program.Γ) (state : GlobalState) (point : Point)
    (hregs : PointRegisters q E) (hwf : state.WF)
    (hout : SmallRange state.mem q.option 168)
    (h29 : SmallRange state.mem q.slot29 166)
    (h30 : SmallRange state.mem q.slot30 166)
    (hp : SmallRange state.mem q.point 160)
    (hco : SmallRange state.mem q.cofactor 160)
    (hid : SmallRange state.mem q.identity 160)
    (hpayload : ReadBytes state (q.option.add 8#64) 160 (layout.point point))
    (hone : ReadBytes state q.one 40 (1#320)) (hd : PointDisjoint q) :
    ∃ after, PointCallTrace p q state after ∧ PointCheckFrame state after q ∧
      (program p g).runFrom E 2 state =
        (program p g).runFrom (pointBlockEnv E q (shared.smallOrder point))
          (if shared.smallOrder point then 12 else 4) after := by
  let copied := optionCopyState state q.option q.slot29 q.slot30 q.point
  have hcopied := option_copy_readback state q.option q.slot29 q.slot30 q.point
    (layout.point point) hpayload h29 h30 hp
  have honeCopied : ReadBytes copied q.one 40 (1#320) :=
    ⟨option_copy_live state q.option q.slot29 q.slot30 q.point q.one 40 hone.1,
      (option_copy_read_frame state q.option q.slot29 q.slot30 q.point q.one 320
        (Range.disjoint_of_id_ne hd.oneSlot29) (Range.disjoint_of_id_ne hd.oneSlot30)
        (Range.disjoint_of_id_ne hd.onePoint)).trans hone.2⟩
  obtain ⟨middle, hmcall, hmframe, hmread⟩ := hmul q.cofactor q.point copied point
    (option_copy_wf state q.option q.slot29 q.slot30 q.point hwf)
    (option_copy_live state q.option q.slot29 q.slot30 q.point q.cofactor 160 hco)
    hcopied (Range.disjoint_of_id_ne hd.cofactorPoint)
  have hmidId := hmframe.live q.identity 160
    (option_copy_live state q.option q.slot29 q.slot30 q.point q.identity 160 hid)
  have hmidOne := OutputFrame.readBytes copied middle q.cofactor q.one 160 40 (1#320)
    hmframe honeCopied (Range.disjoint_of_id_ne hd.oneCofactor)
  have hif := identity_frame middle q.identity hmframe.wellFormed hmidId
  have hir : ReadBytes (identityStoreState middle q.identity) q.identity 160 layout.identity := by
    rw [hidentity]
    exact identity_readback middle q.identity hmidId
  have hcoAfter := OutputFrame.readBytes middle (identityStoreState middle q.identity)
    q.identity q.cofactor 160 160 (layout.cofactor point) hif hmread
    (Range.disjoint_of_id_ne hd.cofactorIdentity)
  obtain ⟨after, hecall, heframe⟩ := hequal q.cofactor q.identity
    (identityStoreState middle q.identity) point hif.wellFormed hcoAfter hir
  refine ⟨after, ⟨middle, _, hmcall, hecall⟩, ?_, ?_⟩
  · refine ⟨heframe.wellFormed, ?_, ?_⟩
    · intro ptr n hn
      exact heframe.live ptr n (hif.live ptr n (hmframe.live ptr n
        (option_copy_live state q.option q.slot29 q.slot30 q.point ptr n hn)))
    · intro ptr w h29d h30d hpd hcd hid
      exact (heframe.read ptr w).trans ((hif.read ptr w hid).trans
        ((hmframe.read ptr w hcd).trans
          (option_copy_read_frame state q.option q.slot29 q.slot30 q.point ptr w h29d h30d hpd)))
  · exact point_check_block p g E q state middle after (shared.smallOrder point)
      hregs hout h29 h30 hp (Range.disjoint_of_id_ne hd.first)
      (Range.disjoint_of_id_ne hd.second) (Range.disjoint_of_id_ne hd.third)
      hmcall hmidId hmidOne.1.fits hmidOne.2 (Ne.symm hd.oneIdentity) hecall

theorem entry_of_sha_contracts_cold_trace {Point Scalar Result : Type}
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
      ColdCallTrace p initial key signature message msg.length challenged multiplied compared ∧
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
  refine ⟨challenged, multiplied, compared, ⟨hccall, hmcall, _, hecall⟩, hc, hchallengeRead, hm, he, ?_⟩
  exact entry_block p g E initial challenged multiplied compared key signature message
    (BitVec.ofNat 64 msg.length) (shared.smallOrder A) hkeyE hsigE hmsgE hlenE hccall
    (hc.live _ _ hready.keyCache hk0) hmcall hid hgm
    (stackSlot_disjoint_caller initial hwf 3 hglobal.1 1280 320).symm hecall

end Agave.Ed25519.Verifier.Execution.Dalek

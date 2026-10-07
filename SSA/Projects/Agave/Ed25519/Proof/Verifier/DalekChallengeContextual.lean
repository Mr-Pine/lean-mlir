import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekChallengeLinked
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeContextualFinalization

/-! Contextual SHA finalization through the exact Dalek entry block.
These are composition proofs reusing the existing instruction and frame lemmas.
Montgomery readiness is required only at the actual challenge call state. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge

/-- The exact linked call, with the initialized IV made explicit, satisfies
the output/frame part of Dalek's challenge contract. The scalar interpretation
is a separate mathematical representation equality. -/
theorem challenge_call_of_sha_contracts_under
    (p : Challenge.Primitives) (g : Challenge.Globals) (sha : Challenge.Sha512Model)
    (sg : ScalarWide.Globals)
    (hcompress : Challenge.CompressContract p.sha512Compress sha)
    (hscalar : SHA512Finalization.ScalarFromSha512ContractUnder
      (ScalarWide.Ready sg) p.scalarFromSha512 sha)
    (layout : Layout Point Scalar Result)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (hencoding : ∀ r a msg, layout.scalar (challenge r a msg) =
      Challenge.digestScalarBytes (sha.digest (Challenge.transcript r a msg)))
    (out key signature message : Pointer) (state : GlobalState)
    (a r : Bytes32) (msg : List (BitVec 8)) (hwf : state.WF)
    (hout : SmallRange state.mem out 32)
    (hkey : ReadBytes state key 32 a) (hsig : ReadBytes state signature 32 r)
    (hmessage : SmallRange state.mem message msg.length)
    (hread : ∀ (i : Nat) (hi : i < msg.length),
      state.mem.readAt (message.add (BitVec.ofNat 64 i)) 8 = msg[i])
    (hlen : msg.length < 2 ^ 63)
    (hiv : ReadBytes state g.address0 64 Challenge.initialWords)
    (hready : ScalarWide.Ready sg state out) :
    ∃ after,
      (Challenge.program p g).call
        (Challenge.challengeArgs out key signature message (BitVec.ofNat 64 msg.length))
        state = .value (.nil, after) ∧
      OutputFrame state after out 32 ∧
      ReadBytes after out 32 (layout.scalar (challenge r a msg)) := by
  have hlen64 : msg.length < 2 ^ 64 := by omega
  have hn : (BitVec.ofNat 64 msg.length).toNat = msg.length :=
    Nat.mod_eq_of_lt hlen64
  obtain ⟨after, hcall, hmem, _, hw⟩ := Challenge.challenge_call_under p g sha sg hcompress hscalar
    state out key signature message (BitVec.ofNat 64 msg.length) r a msg hwf hout
    hkey.1 hsig.1 (by simpa only [hn] using hmessage) hkey.2 hsig.2
    (by simpa only [hn] using challenge_readBytes_of_getElem state message msg hread)
    hiv.1 hiv.2 hready
  refine ⟨after, hcall, challenge_outputFrame_of_store state after out _ hmem hw, ?_, ?_⟩
  · rw [hmem]
    exact hout.storeAt _ _
  · rw [hmem, MemoryState.readAt_storeAt_self hout.fits, hencoding]

/-- Entry execution with the actual extracted challenge call and only a
per-invocation initialized-IV premise. In particular this theorem requires no
universally quantified `ChallengeIVAvailable` or `ChallengeContract` premise. -/
theorem entry_of_sha_contracts_under {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (shared : Shared Point Scalar)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (cp : Challenge.Primitives) (cg : Challenge.Globals) (sha : Challenge.Sha512Model)
    (sg : ScalarWide.Globals)
    (hlink : p.challengeScalar = (Challenge.program cp cg).call)
    (hcompress : Challenge.CompressContract cp.sha512Compress sha)
    (hscalar : SHA512Finalization.ScalarFromSha512ContractUnder
      (ScalarWide.Ready sg) cp.scalarFromSha512 sha)
    (hencoding : ∀ r a msg, layout.scalar (challenge r a msg) =
      Challenge.digestScalarBytes (sha.digest (Challenge.transcript r a msg)))
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
    (hready : ScalarWide.Ready sg (allocated initial) (stackSlot initial 12)) :
    ∃ challenged multiplied compared,
      OutputFrame (allocated initial) challenged (stackSlot initial 12) 32 ∧
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
  obtain ⟨challenged, hccall, hc, hchallengeRead⟩ :=
    challenge_call_of_sha_contracts_under cp cg sha sg hcompress hscalar layout challenge hencoding
      (stackSlot initial 12) key signature message (allocated initial) a r msg
      hwf0 (hstack 12 (by decide))
      ⟨Challenge.smallRange_mono hk0 (by decide),
        (stackState_read initial hwf 13 hk 256).trans ha⟩
      ⟨Challenge.smallRange_mono hs0 (by decide),
        (stackState_read initial hwf 13 hsig 256).trans hr⟩ hm0 hbytes hmlen hiv0 hready
  rw [← hlink] at hccall
  have hAc : ReadBytes challenged (key.add 32) 160 (layout.point A) :=
    hc.readBytes _ _ _ _ _ _ _ hA0
      (stackSlot_disjoint_caller initial hwf 12 hA.1 256 1280).symm
  have hgc : ReadBytes challenged g.address0 40 (1#320) :=
    hc.readBytes _ _ _ _ _ _ _ hg0
      (stackSlot_disjoint_caller initial hwf 12 hglobal.1 256 320).symm
  obtain ⟨multiplied, hmcall, hm, hcofactor⟩ := hmul (stackSlot initial 4) (key.add 32)
    challenged A hc.wellFormed (hc.live _ _ (hstack 4 (by decide))) hAc
    (stackSlot_disjoint_caller initial hwf 4 hA.1 1280 1280)
  have hid : SmallRange multiplied.mem (stackSlot initial 3) 160 :=
    hm.live _ _ (hc.live _ _ (hstack 3 (by decide)))
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
    (hc.live _ _ hk0) hmcall hid hgm
    (stackSlot_disjoint_caller initial hwf 3 hglobal.1 1280 320).symm hecall


end Agave.Ed25519.Verifier.Execution.Dalek

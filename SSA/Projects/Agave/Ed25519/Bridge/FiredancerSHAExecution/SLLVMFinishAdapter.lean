import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMFinishReachable
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerReachableCalls

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer Firedancer.Common
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Bridge.Challenge
namespace FinishCorrect
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A fixed reachable allocation describes an incoming stream in any caller
state containing that allocation. This is only a memory representation premise;
no call outcome or output digest is included. -/
def BlockRepresents (block : LiveBlock) (off : BitVec 64) (completed pending : Bytes) : Prop :=
  ∀ (m : MemoryState) (p : Pointer), m.live? p.id = some block → p.offset = off →
    ContextRepresents m p completed pending


theorem BlockRepresents.of_context {m : MemoryState} {p : Pointer} {block : LiveBlock}
    {off : BitVec 64} {completed pending : Bytes}
    (hp : ContextRepresents m p completed pending) (hb : m.live? p.id = some block)
    (hoff : p.offset = off) (hsmall : block.length < 2^63) :
    BlockRepresents block off completed pending := by
  have hobs := FinishObservation.snapshot_observed hb
  have hr := FinishObservation.snapshot_small (n := 224) hp.live hb hsmall
  have hrep := hobs.context hr hp
  intro m' q hq hqoff
  have hobs' : FinishObservation.Observed m' q (FinishObservation.snapshot block)
      (FinishObservation.snapshotPtr p) := by
    constructor
    · simpa only [FinishObservation.snapshotPtr, FinishObservation.snapshot_get,
        Option.map_some, ofRirBlock] using hq
    · exact hqoff.trans hoff.symm
  obtain ⟨b,hb',hlen⟩ := hp.live
  have hb'' : m.live? p.id = some b := by simp only [MemoryState.live?, hb']
  have he : b = block := Option.some.inj (hb''.symm.trans hb)
  subst b
  have hfits : Fits m' q (224*8) := by
    refine ⟨block,getElem?_of_live? hq,?_⟩
    simpa only [Pointer.offsetInBits, hqoff, hoff] using hlen
  apply hobs'.context_back hfits _ hrep
  simpa only [hqoff, hoff] using hp.noWrap

/-- Actual imported source finalization supplies the verifier's reachable
finish contract directly; the discarded context has no postcondition. -/
theorem reachable_finish
    (hcore : ∀ (s : GlobalState) (kp chain data : Pointer) (count : BitVec 64),
      Core.Ready s kp chain data count → Core.Executes s chain data count)
    (block : LiveBlock) (off : BitVec 64) (completed pending : Bytes)
    (hsmall : block.length < 2^63) (hrep : BlockRepresents block off completed pending) :
    Agave.Ed25519.Bridge.FiredancerReachableFinish programs constantsBytes (some block) off
      (digest Spec.compression (completed ++ pending)) := by
  intro p o s hw ho hnowrap hne hk hks hoff hblock hout houtoff
  have hp := hrep s.mem p hblock hoff
  have hc : Core.SmallRange s.mem p 224 := small_of_fits hp.live (by
    intro b hb
    have he : b = block := Option.some.inj (hb.symm.trans hblock)
    simpa only [he] using hsmall)
  have hor : Core.SmallRange s.mem o 64 :=
    ⟨⟨64,0#_⟩, hout, by decide, by simp [houtoff]⟩
  obtain ⟨after, hrun, hpost⟩ := call_digest_constants hcore s p o completed pending
    hw hc hor (Ne.symm hne) hp hk hks
  refine ⟨after, ?_, hpost.wf, hpost.alloc, hpost.globalsEq, ?_, hpost.outputFits, hpost.output_readWord⟩
  · simpa only [programs_finish, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.singleton] using hrun
  · intro b hb
    exact hpost.frame b (fun he => hb (Or.inl he)) (fun he => hb (Or.inr he))

end FinishCorrect
end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource

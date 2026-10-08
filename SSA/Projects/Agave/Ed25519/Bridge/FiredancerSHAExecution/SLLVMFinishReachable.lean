import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMFinishCorrect

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer Firedancer.Common
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Bridge.Challenge
namespace FinishCorrect
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem small_of_fits {m : MemoryState} {p : Pointer} {n : Nat}
    (hf : Fits m p (8*n))
    (hs : ∀ b, m.live? p.id = some b → b.length < 2^63) : Core.SmallRange m p n := by
  obtain ⟨b,hb,hlen⟩ := hf
  have hlive : m.live? p.id = some b := by simp only [MemoryState.live?, hb]
  refine ⟨b,hlive,hs b hlive,?_⟩
  simp only [Pointer.offsetInBits, LiveBlock.lengthInBits] at hlen
  omega

theorem ready_of_constants (s : GlobalState) (p o : Pointer)
    (hw : s.WF) (hc : Core.SmallRange s.mem p 224) (ho : Core.SmallRange s.mem o 64)
    (hne : o.id ≠ p.id) (hk : Sha512KHolds s p constantsBytes)
    (hs : ∀ q, GlobalPtr s "fd_sha512_core_ref.K" q →
      ∀ b, s.mem.live? q.id = some b → b.length < 2^63) :
    ∃ kp, Ready s p o kp := by
  obtain ⟨kp, ⟨hptr, hkfits, hkread⟩, hksep⟩ := hk
  exact ⟨kp, hw, hc, ho, small_of_fits hkfits (hs kp hptr), hptr,
    (Core.readBits_eq_readWord hkfits).trans hkread, Ne.symm hksep, hne⟩

theorem Post.output_readWord {before after : GlobalState} {p o : Pointer} {message : Bytes}
    (h : Post before after p o message) :
    readWord h.outputFits = digest Spec.compression message := by
  rw [← Core.readBits_eq_readWord h.outputFits, FinishDigest.readBits_sourceRead]
  exact h.output

/-- Verifier-shaped entry interface: the installed K table and incoming stream
representation suffice; the finalizer's output allocation may be any live
separate small block with 64 addressable bytes. -/
theorem call_digest_constants
    (hcore : ∀ (s : GlobalState) (kp chain data : Pointer) (count : BitVec 64),
      Core.Ready s kp chain data count → Core.Executes s chain data count)
    (s : GlobalState) (p o : Pointer) (completed pending : Bytes)
    (hw : s.WF) (hc : Core.SmallRange s.mem p 224) (ho : Core.SmallRange s.mem o 64)
    (hne : o.id ≠ p.id) (hp : ContextRepresents s.mem p completed pending)
    (hk : Sha512KHolds s p constantsBytes)
    (hs : ∀ q, GlobalPtr s "fd_sha512_core_ref.K" q →
      ∀ b, s.mem.live? q.id = some b → b.length < 2^63) :
    ∃ after, StateT.run (runFunction (finish.denote
        (.cons (.value o) (Ctxt.Valuation.singleton (.value p))))) s =
      .value ([.value o]ₕ, after) ∧ Post s after p o (completed ++ pending) := by
  obtain ⟨kp,hr⟩ := ready_of_constants s p o hw hc ho hne hk hs
  exact call_digest hcore s p o kp completed pending hr hp

end FinishCorrect
end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource

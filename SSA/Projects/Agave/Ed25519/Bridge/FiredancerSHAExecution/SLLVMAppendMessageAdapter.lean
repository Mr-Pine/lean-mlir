import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendMessageSnapshot
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendMessageCongruence

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer Firedancer.Common
namespace MessageExecution
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
attribute [local irreducible] append core Core.result sourceRead

/-- A single exact context allocation witnesses the third verifier append in
every caller state with the same initial context and message bytes. -/
theorem reachable_message (before : LiveBlock) (R A message : List (BitVec 8))
    (hlen : before.length = 256) (hR : R.length = 32) (hA : A.length = 32)
    (hp : FinishCorrect.BlockRepresents before 0#64 [] (R ++ A))
    (hmessage : message.length < 2^63) :
    ∃ after : LiveBlock, after.length = 256 ∧
      FiredancerReachableAppend programs constantsBytes (some before) (some after) 0#64 message ∧
      FinishCorrect.BlockRepresents after 0#64
        (StreamSpec.complete (R ++ A ++ message)) (StreamSpec.pending (R ++ A ++ message)) := by
  let s := snapshotState before message
  let n := BitVec.ofNat 64 message.length
  have hn : n.toNat = message.length := by
    simp only [n, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hc := snapshot_context_range before message (by omega) (by omega)
  have hd : Core.SmallRange s.mem snapshotData n.toNat := by
    simpa only [hn] using snapshot_data_range before message hmessage
  have hbytes : sourceReadBytes s.mem snapshotData n.toNat = message := by
    simpa only [hn] using snapshot_bytes before message hmessage
  have hrep : ContextRepresents s.mem snapshotContext [] (R ++ A) :=
    hp s.mem snapshotContext (snapshot_context before message) rfl
  have hcount : sourceRead s.mem (snapshotContext.withOffset 200#64) 64 = 64#64 := by
    simpa only [List.length_append, hR, hA] using hrep.pendingCount
  have hsmall (m : MemoryState) (p : Pointer) (bytes : Nat) (h : Core.SmallRange m p bytes) :
      ∀ b, m.live? p.id = some b → b.length < 2^63 := by
    obtain ⟨b, hb, hs, _⟩ := h
    intro b' hb'
    have he : b' = b := Option.some.inj (hb'.symm.trans hb)
    simpa only [he] using hs
  have hout := append_message_result_represents_source s snapshotContext snapshotData n
    [] (R ++ A) hrep hd.fits (by decide) (hsmall _ _ _ hc) (hsmall _ _ _ hd) hcount
  rw [hbytes] at hout
  simp only [List.nil_append] at hout
  obtain ⟨after, hb, _⟩ := hout.live
  have hafter : (resultState s snapshotContext snapshotData n).mem.live? snapshotContext.id = some after := by
    simp only [MemoryState.live?, hb]
  have hlength := resultState_context_length s snapshotContext snapshotData n
  rw [hafter, snapshot_context, Option.map_some, Option.map_some] at hlength
  have hal : after.length = 256 := (Option.some.inj hlength).trans hlen
  refine ⟨after, hal, ?_, FinishCorrect.BlockRepresents.of_context hout hafter rfl (by omega)⟩
  intro p data sz t hw _ hsep hk hfit hds hks hoff hblock hinput
  have hslen : sz.toNat = message.length := by
    simpa only [bytesOf, List.length_ofFn] using congrArg List.length hinput
  have hsz : sz = n := BitVec.eq_of_toNat_eq (hslen.trans hn.symm)
  subst sz
  have htcontext : Core.SmallRange t.mem p 224 :=
    ⟨before, hblock, by omega, by simp only [hoff, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_add]; omega⟩
  have htdata : Core.SmallRange t.mem data n.toNat :=
    FinishCorrect.small_of_fits (by simpa only [Nat.mul_comm] using hfit) hds
  obtain ⟨kp, ⟨hkptr, hkfit, hkvalue⟩, hksep⟩ := hk
  have hready : Ready t p data kp n :=
    ⟨hw, htcontext, htdata, FinishCorrect.small_of_fits hkfit (hks kp hkptr),
      hkptr, (Core.readBits_eq_readWord hkfit).trans hkvalue, hksep.symm, hsep⟩
  have htbytes : sourceReadBytes t.mem data n.toNat = message := by
    rw [← FinishDigest.readBytes_sourceReadBytes _ _ _ htdata]
    unfold Core.readBytes
    rw [Core.readBits_eq_readWord hfit]
    exact hinput
  have htcount : sourceRead t.mem (p.withOffset 200#64) 64 = 64#64 := by
    simpa only [List.length_append, hR, hA] using (hp t.mem p hblock hoff).pendingCount
  obtain ⟨out, hrun, hwout, ha, hg, hm, hf⟩ := executes t p data kp n hready htcount
  refine ⟨out, ?_, hwout, ha, hg, hf, ?_⟩
  · simpa only [programs_append] using hrun
  · exact (hm p.id).trans ((resultState_context_congr n hoff
      (hblock.trans (snapshot_context before message).symm) hsep (by decide)
      htdata hd (htbytes.trans hbytes.symm)).trans hafter)

end MessageExecution
end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource

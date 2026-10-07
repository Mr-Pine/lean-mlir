import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionCompressionPrivate

/-! The odd prologue compression, preserving arbitrary ABI block count. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

theorem bulk_odd_from_pairs (g : Globals) (E : Env program.Γ)
    (mem : GlobalState) (scratch k chain : Pointer)
    (block : Bytes) (initial : Spec.State) (mark : Nat)
    (hprivate : mark ≤ scratch.id.id)
    (h : PairReady E scratch k 0 0 (specWindow block 0) initial)
    (hs : PairScratch mem.mem scratch (schedule block) 0 0)
    (hk : PairConstants mem.mem k) (hg : GroupReady E 0) (hl : PairLoopConstants E)
    (hd : (Range.of scratch 1024).Disjoint (Range.of k 5120))
    (hf : FeedForwardReady E chain) (hc : SmallRange mem.mem chain 64)
    (hchain : mem.mem.readAt chain 512 = pack initial)
    (hcs : (Range.of scratch 1024).Disjoint (Range.of chain 512)) :
    ∃ E' scratchState,
      ExecTrace (program g) 56 E 5 mem E' 1
        { scratchState with mem := scratchState.mem.storeAt chain (pack (compressBlock initial block)) } ∧
      ScratchFrame scratch mem scratchState ∧
      scratchState.mem.eraseFrom mark = mem.mem.eraseFrom mark ∧
      RegFrame 86 320 E E' ∧ E'.read (%86) = .value 1#64 := by
  obtain ⟨Et, mt, hprefix, htail, hsched, hframe, hmem, herase⟩ :=
    prefix_sixtyfour_private g E mem scratch k block initial mark hprivate
      h hs hk hg hl hd
  have hc' := hmem.live hc
  have hchain' : mt.mem.readAt chain 512 = pack initial :=
    (hmem.read chain 512 hcs).trans hchain
  obtain ⟨Ef, htrace, hfinal, htailframe⟩ :=
    tail_sixteen_from_prefix mt scratch (schedule block) Et initial hsched htail
  let Eout := (feedForwardEnv Ef initial (roundsFrom initial (schedule block) 0 80))[%86 := .value 1#64]
  have hstore := feedForward_block Ef mt chain initial _
    ((hf.of_groupFrame hframe).of_tailFrame htailframe) hfinal hc' hchain'
  change program.bb7.run program.blockParams Ef mt = .value ((Eout, .inr 1),
    {mt with mem := mt.mem.storeAt chain (pack (compressBlock initial block))}) at hstore
  have hff : RegFrame 309 320 Ef (feedForwardEnv Ef initial
      (roundsFrom initial (schedule block) 0 80)) := by
    unfold feedForwardEnv
    repeat' (apply RegFrame.write <;> try decide)
    exact RegFrame.refl _ _ Ef
  have htailframe' : RegFrame 272 308 Et Ef := htailframe
  have hout : RegFrame 86 320 E Eout := by
    apply RegFrame.write
    · exact ((hframe.enlarge (by decide) (by decide)).trans
        (htailframe'.enlarge (by decide) (by decide))).trans
          (hff.enlarge (by decide) (by decide))
    · decide
    · decide
  exact ⟨Eout, mt, (hprefix.trans (htrace.execTrace g)).trans
    (ExecTrace.single hstore), hmem, herase, hout, by simp [Eout, mlir_env]⟩

end Agave.Ed25519.SHA512.Execution.Avx2

import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionCompression
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPrivateFrame
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionReturn

/-! Preserve the count-one return inputs and the private-memory erasure through
the exact imported eighty-round compression trace. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

/-- The outer-loop inputs inherited by every compression iteration. -/
structure ReturnSeed (E : Env program.Γ) (buffer : Pointer) : Prop where
  count : E.read (%arg2) = .value 1#64
  bufferPtr : E.read (%82) = .value buffer
  offset : E.read (%47) = .value 128#64
  byteZero : E.read (%48) = .value 0#8
  length : E.read (%49) = .value 512#64
  one : E.read (%1) = .value 1#64
  zero : E.read (%2) = .value 0#64

theorem ReturnSeed.of_groupFrame {E E' : Env program.Γ} {buffer : Pointer}
    (h : ReturnSeed E buffer) (hf : GroupFrame E E') : ReturnSeed E' buffer := by
  constructor
  · exact (hf.read (%arg2)).trans h.count
  · exact (hf.read (%82)).trans h.bufferPtr
  · exact (hf.read (%47)).trans h.offset
  · exact (hf.read (%48)).trans h.byteZero
  · exact (hf.read (%49)).trans h.length
  · exact (hf.read (%1)).trans h.one
  · exact (hf.read (%2)).trans h.zero

theorem ReturnSeed.of_tailFrame {E E' : Env program.Γ} {buffer : Pointer}
    (h : ReturnSeed E buffer) (hf : TailFrame E E') : ReturnSeed E' buffer := by
  have hr : RegFrame 272 308 E E' := hf
  constructor
  · exact (hr.read (%arg2)).trans h.count
  · exact (hr.read (%82)).trans h.bufferPtr
  · exact (hr.read (%47)).trans h.offset
  · exact (hr.read (%48)).trans h.byteZero
  · exact (hr.read (%49)).trans h.length
  · exact (hr.read (%1)).trans h.one
  · exact (hr.read (%2)).trans h.zero

theorem ReturnSeed.feedForward {E : Env program.Γ} {buffer : Pointer}
    (h : ReturnSeed E buffer) (initial final : Spec.State) :
    ReturnReady ((feedForwardEnv E initial final)[%86 := .value 1#64]) buffer := by
  have hcount := h.count
  change E.args 2 = .value 1#64 at hcount
  constructor <;> simp [feedForwardEnv, mlir_env, hcount, h.bufferPtr,
    h.offset, h.byteZero, h.length, h.one, h.zero]

/-- The original compression region executes 56 blocks, preserves all return
inputs, and changes only the private scratch allocation before feed-forward. -/
theorem compression_from_pairs_private (g : Globals) (E : Env program.Γ)
    (mem : GlobalState) (scratch k chain buffer : Pointer)
    (block : Bytes) (initial : Spec.State) (mark : Nat)
    (hprivate : mark ≤ scratch.id.id)
    (h : PairReady E scratch k 0 0 (specWindow block 0) initial)
    (hs : PairScratch mem.mem scratch (schedule block) 0 0)
    (hk : PairConstants mem.mem k) (hg : GroupReady E 0) (hl : PairLoopConstants E)
    (hd : (Range.of scratch 1024).Disjoint (Range.of k 5120))
    (hf : FeedForwardReady E chain) (hc : SmallRange mem.mem chain 64)
    (hchain : mem.mem.readAt chain 512 = pack initial)
    (hcs : (Range.of scratch 1024).Disjoint (Range.of chain 512))
    (hret : ReturnSeed E buffer) :
    ∃ E' scratchState,
      ExecTrace (program g) 56 E 5 mem E' 1
        { scratchState with mem := scratchState.mem.storeAt chain (pack (compressBlock initial block)) } ∧
      ScratchFrame scratch mem scratchState ∧
      scratchState.mem.eraseFrom mark = mem.mem.eraseFrom mark ∧
      ReturnReady E' buffer := by
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
  exact ⟨Eout, mt, (hprefix.trans (htrace.execTrace g)).trans
    (ExecTrace.single hstore), hmem, herase,
    ((hret.of_groupFrame hframe).of_tailFrame htailframe).feedForward initial _⟩

end Agave.Ed25519.SHA512.Execution.Avx2

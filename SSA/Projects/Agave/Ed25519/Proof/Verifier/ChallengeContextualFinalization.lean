import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionLinked
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Ready

/-!
The actual challenge call from the contextual finalizer contract. The reducer
tables are assumed initialized only in this invocation's initial memory. The
already-proved prefix frame and the actual context copy preserve them up to
the finalizer call. There is no universal global-availability premise.

The full-block compressor keeps its existing interface. DalekChallengeContextual,
DalekExecutionContextual and LinkedContextualLeaves consume this local result;
the older generic linked endpoint retains its original finalizer interface.
-/
namespace Agave.Ed25519.Verifier.Execution.Challenge
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge Agave.Ed25519.Bridge.Challenge

theorem challenge_call_under
    (p : Primitives) (g : Globals) (sha : Sha512Model) (sg : ScalarWide.Globals)
    (hcompress : CompressContract p.sha512Compress sha)
    (hscalar : SHA512Finalization.ScalarFromSha512ContractUnder
      (ScalarWide.Ready sg) p.scalarFromSha512 sha)
    (s : GlobalState) (dst aptr rptr msg : Pointer)
    (n : BitVec 64) (r a : BitVec 256) (message : Bytes)
    (hwf : s.WF) (hout : SmallRange s.mem dst 32)
    (ha : SmallRange s.mem aptr 32) (hr : SmallRange s.mem rptr 32)
    (hinput : SmallRange s.mem msg n.toNat)
    (har : s.mem.readAt aptr 256 = a) (hrr : s.mem.readAt rptr 256 = r)
    (hm : readBytes s.mem msg n.toNat = message)
    (hiv : SmallRange s.mem g.address0 64)
    (hivr : s.mem.readAt g.address0 512 = initialWords)
    (hready : ScalarWide.Ready sg s dst) :
    ∃ after,
      (program p g).call (challengeArgs dst aptr rptr msg n) s = .value (.nil, after) ∧
      after.mem = s.mem.storeAt dst (digestScalarBytes (sha.digest (transcript r a message))) ∧
      (after.mem.readAt dst 256).toNat = (sha.digest (transcript r a message)).toNat % subgroupOrder ∧
      after.WF := by
  let args := challengeArgs dst aptr rptr msg n
  obtain ⟨F, t, completed, pending, hprefix, hregs, hctx, hbytes, hresources, htwf, hframe⟩ :=
    challenge_reaches_final p g sha hcompress (Env.init args.get) s dst aptr rptr msg n r a message
      (by simp [args, challengeArgs, mlir_env, Env.init, Vals.get])
      (by simp [args, challengeArgs, mlir_env, Env.init, Vals.get])
      (by simp [args, challengeArgs, mlir_env, Env.init, Vals.get])
      (by simp [args, challengeArgs, mlir_env, Env.init, Vals.get])
      (by simp [args, challengeArgs, mlir_env, Env.init, Vals.get])
      hwf hout ha hr hinput har hrr hm hiv hivr
  let copied : GlobalState :=
    {t with mem := t.mem.storeAt (finalSlot s) (t.mem.readAt (contextSlot s) 1664)}
  have hcopyframe : copied.mem.eraseFrom s.alloc.nextFreeBlock = s.mem :=
    erase_internal_store t.mem s.mem s.alloc.nextFreeBlock (finalSlot s)
      (t.mem.readAt (contextSlot s) 1664) hframe (final_internal s)
  have hcopyready : ScalarWide.Ready sg copied dst :=
    SHA512Finalization.ready_of_frame sg s copied dst s.alloc.nextFreeBlock hcopyframe hready
  have hcopyctx : ContextRepresents sha copied.mem (finalSlot s) completed pending :=
    ContextRepresents.copy sha t.mem (contextSlot s) (finalSlot s)
      completed pending hctx hresources.copy
  obtain ⟨last, hcall, heffect⟩ := hscalar copied dst (finalSlot s) completed pending
    htwf.storeAt hcopyready (hresources.output.storeAt _ _) hcopyctx
    (Or.inl (final_ne_caller hwf hout).symm)
  have hfinal := final_block p g F t last dst (contextSlot s) (finalSlot s)
    hregs.output hregs.context hregs.scratch hregs.bytes hctx.live.fits hresources.copy.fits
    (Or.inl (final_ne_context s)) hcall
  have hrun : (program p g).run args s = .value (.nil, last) := by
    rw [Func.run_runFrom_eq]
    exact hprefix.trans hfinal
  have hlastwf : last.WF := heffect.wellFormed htwf.storeAt
  have hlastframe : last.mem.eraseFrom s.alloc.nextFreeBlock =
      s.mem.storeAt dst (digestScalarBytes (sha.digest (transcript r a message))) := by
    rw [heffect.memory, MemoryState.eraseFrom_storeAt, hcopyframe, ← hbytes]
  let after : GlobalState := {last with mem := last.mem.eraseFrom s.alloc.nextFreeBlock}
  refine ⟨after, Func.call_of_run hrun, hlastframe, ?_, ?_⟩
  · change ((last.mem.eraseFrom s.alloc.nextFreeBlock).readAt dst 256).toNat = _
    rw [hlastframe, MemoryState.readAt_storeAt_self hout.fits, digestScalarBytes_toNat]
  · intro k hk
    exact hlastwf k (Std.ExtHashMap.mem_of_mem_filter hk)

end Agave.Ed25519.Verifier.Execution.Challenge

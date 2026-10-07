import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionPrefix

namespace Agave.Ed25519.Verifier.Execution.Challenge

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge Agave.Ed25519.Bridge.Challenge

def challengeArgs (dst aptr rptr message : Pointer) (length : BitVec 64) :
    Vals [.ptr, .ptr, .ptr, .ptr, .bv 64] :=
  .cons (.value dst) (.cons (.value aptr) (.cons (.value rptr)
    (.cons (.value message) (.cons (.value length) .nil))))

/-- Linked refinement of the actual imported `challenge_scalar` callee,
including frame cleanup. Its complete observable memory effect is the 32-byte
encoding of SHA-512(R || A || message) reduced modulo the subgroup order.

The SHA-512 compression primitive is specified only on full blocks. The
`scalar_from_sha512` primitive explicitly owns padding, digest serialization,
and little-endian reduction; none of that absent implementation is claimed to
be proved by this caller theorem. -/
theorem challenge_call (p : Primitives) (g : Globals) (sha : Sha512Model)
    (hcompress : CompressContract p.sha512Compress sha)
    (hscalar : ScalarFromSha512Contract p.scalarFromSha512 sha)
    (s : GlobalState) (dst aptr rptr msg : Pointer)
    (n : BitVec 64) (r a : BitVec 256) (message : Bytes)
    (hwf : s.WF) (hout : SmallRange s.mem dst 32)
    (ha : SmallRange s.mem aptr 32) (hr : SmallRange s.mem rptr 32)
    (hinput : SmallRange s.mem msg n.toNat)
    (har : s.mem.readAt aptr 256 = a) (hrr : s.mem.readAt rptr 256 = r)
    (hm : readBytes s.mem msg n.toNat = message)
    (hiv : SmallRange s.mem g.address0 64)
    (hivr : s.mem.readAt g.address0 512 = initialWords) :
    ∃ after,
      (program p g).call (challengeArgs dst aptr rptr msg n) s = .value (.nil, after) ∧
      after.mem = s.mem.storeAt dst (digestScalarBytes (sha.digest (transcript r a message))) ∧
      (after.mem.readAt dst 256).toNat = (sha.digest (transcript r a message)).toNat % subgroupOrder ∧
      after.WF := by
  let args := challengeArgs dst aptr rptr msg n
  obtain ⟨last, hrun, hframe, hw⟩ := challenge_runFrom p g sha hcompress hscalar
    (Env.init args.get) s dst aptr rptr msg n r a message
    (by simp [args, challengeArgs, mlir_env, Env.init, Vals.get])
    (by simp [args, challengeArgs, mlir_env, Env.init, Vals.get])
    (by simp [args, challengeArgs, mlir_env, Env.init, Vals.get])
    (by simp [args, challengeArgs, mlir_env, Env.init, Vals.get])
    (by simp [args, challengeArgs, mlir_env, Env.init, Vals.get])
    hwf hout ha hr hinput har hrr hm hiv hivr
  have hrun' : (program p g).run args s = .value (.nil, last) := by
    rw [Func.run_runFrom_eq]
    exact hrun
  let after : GlobalState := {last with mem := last.mem.eraseFrom s.alloc.nextFreeBlock}
  refine ⟨after, Func.call_of_run hrun', hframe, ?_, ?_⟩
  · change ((last.mem.eraseFrom s.alloc.nextFreeBlock).readAt dst 256).toNat = _
    rw [hframe, MemoryState.readAt_storeAt_self hout.fits, digestScalarBytes_toNat]
  · intro k hk
    exact hw k (Std.ExtHashMap.mem_of_mem_filter hk)

end Agave.Ed25519.Verifier.Execution.Challenge

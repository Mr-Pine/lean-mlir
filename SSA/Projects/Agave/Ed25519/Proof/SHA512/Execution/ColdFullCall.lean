import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Entry
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.ColdPaddedBranches
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.FinalBlock
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Ready

namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Challenge
open Agave.Ed25519.SHA512

set_option maxRecDepth 24000
set_option maxHeartbeats 2400000

/-- Execute all four imported blocks. Primitive assumptions are restricted to
one complete compression block and the exact invocation-local wide reducer. -/
theorem finalizer_run_cold (g : CompressionGlobals) (r : ScalarWide.Globals)
    (p : Primitives) (compress : Compression)
    (hcompress : OneBlockCompressContractUnder g p.sha512Compress compress)
    (hreduce : ReduceWideContractUnder (ScalarWide.Ready r) p.reduceWide)
    (E : Env program.Γ) (s : GlobalState) (out src : Pointer)
    (completed pending : Bytes)
    (heout : E.read (%arg0) = .value out) (hesrc : E.read (%arg1) = .value src)
    (hwf : s.WF) (hr : ColdFinalizerReady g r s out src) (ho : SmallRange s.mem out 32)
    (hctx : ContextRepresents (model compress) s.mem src completed pending) :
    ∃ after,
      (program p).runFrom E 0 s = .value (.nil, after) ∧
      CacheFrame g (s.mem.storeAt out (digestScalarBytes (digest compress (completed ++ pending))))
        (after.mem.eraseFrom s.alloc.nextFreeBlock) ∧
      s.alloc.nextFreeBlock ≤ after.alloc.nextFreeBlock := by
  let count := s.mem.readAt (src.add 127#64) 8
  let blocks := s.mem.readAt (src.add 192#64) 128
  let F := entryEnv E s count blocks
  let S := entryState s src count
  let long := needsTwoBlocks count
  let total := completed.length + pending.length
  have hcountNat : count.toNat = pending.length := hctx.pendingCount
  have hblocksNat : blocks.toNat = completed.length / 128 := hctx.blockCount
  have hp : count.toNat < 128 := by rw [hcountNat]; exact hctx.pendingBound
  have ht : 128 * blocks.toNat + count.toNat = total := by
    rw [hblocksNat, hcountNat]
    have := hctx.completedWhole
    dsimp [total]
    omega
  have hentry := entry_block p E s src count blocks hesrc hwf hctx.live rfl rfl hp
  have hb : readBytes S.mem (slot s 3) 128 = firstPaddingBlock pending :=
    paddingState_bytes (model compress) (allocateSlots s slotSizes) src (slot s 5)
      (slot s 3) completed pending count (allocated_context s src _ _ _ hwf hctx)
      (locals_allocated s hwf).context (locals_allocated s hwf).buffer
      (slot_ne s 3 5 (by decide) (by decide) (by decide)) hctx.pendingCount
  have hchoice : long = true ↔ 112 ≤ pending.length := by
    rw [← hcountNat]
    exact needsTwoBlocks_iff count hp
  obtain ⟨middle, hm⟩ := padded_branches_cold g p compress hcompress s S F out pending total long
    hchoice hctx.pendingBound
    (by simp [F, entryEnv, paddingEnv, allocatedEnv, mlir_env])
    (by simp [F, entryEnv, paddingEnv, allocatedEnv, mlir_env])
    (by simp [F, entryEnv, paddingEnv, allocatedEnv, mlir_env])
    (by simp [F, entryEnv, paddingEnv, allocatedEnv, mlir_env])
    (by simp [F, entryEnv, paddingEnv, allocatedEnv, mlir_env])
    (by simp [F, entryEnv, paddingEnv, allocatedEnv, mlir_env, ht])
    (by simp [F, entryEnv, paddingEnv, allocatedEnv, mlir_env])
    (by simp [F, entryEnv, paddingEnv, allocatedEnv, mlir_env])
    (by simp [F, entryEnv, paddingEnv, allocatedEnv, mlir_env])
    (by simp [F, entryEnv, paddingEnv, allocatedEnv, mlir_env])
    (entryState_wf s src count hwf) (entryState_locals s src count hwf)
    (entryState_live s src out count hwf ho) hb
    (by rw [entryState_frame s src count hwf]; exact CacheFrame.refl g s.mem hr.compression.cache)
    (CompressionReady.of_frame g s S s.alloc.nextFreeBlock (entryState_frame s src count hwf) hr.compression)
    (hr.compression.cache_lt hwf) (hr.compression.constants_lt hwf) hr.outputCache
  have hserializedFrame : CacheFrame g s.mem
      ((serializedState middle (slot s 5) (slot s 4)).mem.eraseFrom s.alloc.nextFreeBlock) := by
    rw [serializedState_frame _ _ _ _ (slot_internal s 5 (by decide)) (slot_internal s 4 (by decide))]
    exact hm.frame
  have hready : ScalarWide.Ready r (serializedState middle (slot s 5) (slot s 4)) out :=
    scalarReady_of_cacheFrame g r s _ out s.alloc.nextFreeBlock hserializedFrame hr.reduction
      hr.reduceRCache hr.reduceRRCache
  let G := branchEnv F s long
  have envEq : ∀ (i : Fin 64), G.read (scratchReg i) = .value (slot s (i.val + 6)) := by
    intro i
    fin_cases i <;> cases hlong : long <;>
      simp [G, branchEnv, F, entryEnv, paddingEnv, allocatedEnv, scratchReg, mlir_env, hlong]
  obtain ⟨after, hrun, hframe, hcounter, _⟩ := final_block_of_contract p (ScalarWide.Ready r) hreduce
    G middle (slot s 5) (slot s 4) out (fun i => slot s (i.val + 6)) s.alloc.nextFreeBlock
    (by cases hlong : long <;> simp [G, branchEnv, F, entryEnv, paddingEnv, allocatedEnv, mlir_env, hlong])
    (by cases hlong : long <;> simp [G, branchEnv, F, entryEnv, paddingEnv, allocatedEnv, mlir_env, hlong])
    (by cases hlong : long <;> simp [G, branchEnv, F, entryEnv, paddingEnv, allocatedEnv, mlir_env, hlong])
    (by cases hlong : long <;> simp [G, branchEnv, F, entryEnv, paddingEnv, allocatedEnv, mlir_env, hlong])
    (by cases hlong : long <;> simpa [G, branchEnv, F, entryEnv, paddingEnv, allocatedEnv, mlir_env, hlong] using heout)
    (by cases hlong : long <;> simp [G, branchEnv, F, entryEnv, paddingEnv, allocatedEnv, mlir_env, hlong])
    envEq hm.wf hm.locals.context hm.locals.digest hm.output hm.locals.scratch
    (Or.inl (slot_ne_caller s 4 (by decide) out hwf ho).symm) hready
    (slot_internal s 5 (by decide)) (slot_internal s 4 (by decide))
    (fun i => slot_internal s (i.val + 6) (by omega))
  have hchainInitial : S.mem.readAt ((slot s 5).add 128#64) 512 =
      compress.run initialWords completed :=
    (entryState_chaining s src count hwf hctx.live).trans hctx.chaining
  refine ⟨after, hentry.trans (hm.run.trans hrun), ?_, ?_⟩
  · rw [hm.chain, hchainInitial] at hframe
    change after.mem.eraseFrom s.alloc.nextFreeBlock =
      (middle.mem.eraseFrom s.alloc.nextFreeBlock).storeAt out
        (digestScalarBytes (finalize compress (compress.run initialWords completed) pending total)) at hframe
    rw [finalize_eq_digest compress completed pending hctx.completedWhole hctx.pendingBound] at hframe
    rw [hframe]
    exact hm.frame.storeAt out _ hr.outputCache
  · have hi : s.alloc.nextFreeBlock ≤ S.alloc.nextFreeBlock := by
      dsimp [S]
      rw [entryState_counter]
      omega
    exact hi.trans (hm.counter.trans hcounter)

/-- Cold-capable finalizer ABI with all invocation-local global requirements
and the exact expected scalar output. Only the designated cache byte may also
change; every other block is preserved outside the output range. -/
def ScalarFromSha512ColdContract (g : CompressionGlobals) (r : ScalarWide.Globals)
    (call : Vals [.ptr, .ptr] → EffectM (Vals [])) (compress : Compression) : Prop :=
  ∀ s out src completed pending, s.WF → ColdFinalizerReady g r s out src →
    SmallRange s.mem out 32 → ContextRepresents (model compress) s.mem src completed pending →
    ∃ after,
      call (.cons (.value out) (.cons (.value src) .nil)) s = .value (.nil, after) ∧
      CacheOutputEffect g s after out (digestScalarBytes (digest compress (completed ++ pending)))

theorem finalizer_contract_cold (g : CompressionGlobals) (r : ScalarWide.Globals)
    (p : Primitives) (compress : Compression)
    (hcompress : OneBlockCompressContractUnder g p.sha512Compress compress)
    (hreduce : ReduceWideContractUnder (ScalarWide.Ready r) p.reduceWide) :
    ScalarFromSha512ColdContract g r (program p).call compress := by
  intro s out src completed pending hwf hr ho hc
  let args : Vals [.ptr, .ptr] := .cons (.value out) (.cons (.value src) .nil)
  obtain ⟨after, hrun, hframe, hcounter⟩ := finalizer_run_cold g r p compress
    hcompress hreduce (Env.init args.get) s out src completed pending
    (by simp [args, Env.init, Vals.get, mlir_env])
    (by simp [args, Env.init, Vals.get, mlir_env]) hwf hr ho hc
  have hrun' : (program p).run args s = .value (.nil, after) := by
    rw [Func.run_runFrom_eq]
    exact hrun
  exact ⟨_, Func.call_of_run hrun', ⟨hframe, hcounter⟩⟩

/-- Warm-cache invocation recovers the same exact output-only StoreEffect
used by the existing finalizer theorem. Stability follows from the composed
CacheTransition, not an extra unchanged-cache postcondition. -/
theorem finalizer_call_warm (g : CompressionGlobals) (r : ScalarWide.Globals)
    (p : Primitives) (compress : Compression)
    (hcompress : OneBlockCompressContractUnder g p.sha512Compress compress)
    (hreduce : ReduceWideContractUnder (ScalarWide.Ready r) p.reduceWide)
    (s : GlobalState) (out src : Pointer) (completed pending : Bytes)
    (hwf : s.WF) (hr : ColdFinalizerReady g r s out src) (hwarm : CacheWarm g s)
    (ho : SmallRange s.mem out 32)
    (hc : ContextRepresents (model compress) s.mem src completed pending) :
    ∃ after,
      (program p).call (.cons (.value out) (.cons (.value src) .nil)) s = .value (.nil, after) ∧
      StoreEffect s after out (digestScalarBytes (digest compress (completed ++ pending))) := by
  obtain ⟨after, hcall, he⟩ := finalizer_contract_cold g r p compress hcompress hreduce
    s out src completed pending hwf hr ho hc
  exact ⟨after, hcall, he.warm hr.compression hr.outputCache hwarm⟩

/-- Concrete linked scalar reduction is still isolated at its own execution
obligation; no whole-finalizer or whole-challenge premise is introduced. -/
theorem linked_finalizer_cold (g : CompressionGlobals) (r : ScalarWide.Globals)
    (compress : Compression) (call : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (hcompress : OneBlockCompressContractUnder g call compress)
    (hreduce : ScalarWide.ExecutionObligation r) :
    ScalarFromSha512ColdContract g r (program (ScalarWide.finalizationPrimitives r call)).call compress :=
  finalizer_contract_cold g r _ compress hcompress (linkedReduceWide_of_execution r hreduce)

end Agave.Ed25519.Verifier.Execution.SHA512Finalization

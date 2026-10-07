import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Entry
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.PaddedBranches
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.FinalBlock
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Ready

namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Challenge
open Agave.Ed25519.SHA512

/-- Immutable global prerequisites survive work confined to a fresh frame. -/
def FrameStable (ready : GlobalState → Pointer → Prop) : Prop :=
  ∀ before after out mark, after.mem.eraseFrom mark = before.mem →
    ready before out → ready after out

set_option maxRecDepth 24000
set_option maxHeartbeats 2400000

/-- Execute all four imported blocks. Primitive assumptions are restricted to
one complete compression block and the exact invocation-local wide reducer. -/
theorem finalizer_run (p : Primitives) (compress : Compression)
    (ready : GlobalState → Pointer → Prop) (hstable : FrameStable ready)
    (hcompress : OneBlockCompressContract p.sha512Compress compress)
    (hreduce : ReduceWideContractUnder ready p.reduceWide)
    (E : Env program.Γ) (s : GlobalState) (out src : Pointer)
    (completed pending : Bytes)
    (heout : E.read (%arg0) = .value out) (hesrc : E.read (%arg1) = .value src)
    (hwf : s.WF) (hr : ready s out) (ho : SmallRange s.mem out 32)
    (hctx : ContextRepresents (model compress) s.mem src completed pending) :
    ∃ after,
      (program p).runFrom E 0 s = .value (.nil, after) ∧
      after.mem.eraseFrom s.alloc.nextFreeBlock =
        s.mem.storeAt out (digestScalarBytes (digest compress (completed ++ pending))) ∧
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
  obtain ⟨middle, hm⟩ := padded_branches p compress hcompress s S F out pending total long
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
    (entryState_live s src out count hwf ho) hb (entryState_frame s src count hwf)
  have hready : ready (serializedState middle (slot s 5) (slot s 4)) out :=
    hstable s _ out s.alloc.nextFreeBlock
      ((serializedState_frame middle (slot s 5) (slot s 4) s.alloc.nextFreeBlock
        (slot_internal s 5 (by decide)) (slot_internal s 4 (by decide))).trans hm.frame) hr
  let G := branchEnv F s long
  have envEq : ∀ (i : Fin 64), G.read (scratchReg i) = .value (slot s (i.val + 6)) := by
    intro i
    fin_cases i <;> cases hlong : long <;>
      simp [G, branchEnv, F, entryEnv, paddingEnv, allocatedEnv, scratchReg, mlir_env, hlong]
  obtain ⟨after, hrun, hframe, hcounter, _⟩ := final_block_of_contract p ready hreduce
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
  · rw [hm.frame, hm.chain, hchainInitial] at hframe
    change after.mem.eraseFrom s.alloc.nextFreeBlock =
      s.mem.storeAt out (digestScalarBytes (finalize compress
        (compress.run initialWords completed) pending total)) at hframe
    rw [finalize_eq_digest compress completed pending hctx.completedWhole hctx.pendingBound] at hframe
    exact hframe
  · have hi : s.alloc.nextFreeBlock ≤ S.alloc.nextFreeBlock := by
      dsimp [S]
      rw [entryState_counter]
      omega
    exact hi.trans (hm.counter.trans hcounter)

/-- Exact call contract, after the RIR function-call cleanup removes the
seventy local allocations and all allocations made by its callees. -/
theorem finalizer_contract_under (p : Primitives) (compress : Compression)
    (ready : GlobalState → Pointer → Prop) (hstable : FrameStable ready)
    (hcompress : OneBlockCompressContract p.sha512Compress compress)
    (hreduce : ReduceWideContractUnder ready p.reduceWide) :
    ScalarFromSha512ContractUnder ready (program p).call (model compress) := by
  intro s out src completed pending hwf hr ho hc _
  let args : Vals [.ptr, .ptr] := .cons (.value out) (.cons (.value src) .nil)
  obtain ⟨after, hrun, hframe, hcounter⟩ := finalizer_run p compress ready hstable
    hcompress hreduce (Env.init args.get) s out src completed pending
    (by simp [args, Env.init, Vals.get, mlir_env])
    (by simp [args, Env.init, Vals.get, mlir_env]) hwf hr ho hc
  have hrun' : (program p).run args s = .value (.nil, after) := by
    rw [Func.run_runFrom_eq]
    exact hrun
  exact ⟨_, Func.call_of_run hrun', ⟨hframe, hcounter⟩⟩

/-- The original generic all-state contract follows from the generic local
reducer contract. No extra length bound is imposed. -/
theorem finalizer_contract (p : Primitives) (compress : Compression)
    (hcompress : OneBlockCompressContract p.sha512Compress compress)
    (hreduce : ReduceWideContract p.reduceWide) :
    ScalarFromSha512Contract (program p).call (model compress) :=
  (scalarFromSha512_unrestricted _ _).mp
    (finalizer_contract_under p compress (fun _ _ => True)
      (by unfold FrameStable; intros; trivial) hcompress ((reduceWide_unrestricted _).mpr hreduce))

/-- The globally linked reducer uses its real Montgomery-table prerequisite
at finalizer entry, preserved until the invocation-local reduction call. -/
theorem linked_finalizer_contract (compress : Compression)
    (call : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (g : ScalarWide.Globals) (hcompress : OneBlockCompressContract call compress)
    (hreduce : LinkedReduceWideContract g) :
    ScalarFromSha512ContractUnder (ScalarWide.Ready g)
      (program ⟨call, (ScalarWide.linkedProgram g).call⟩).call (model compress) :=
  finalizer_contract_under _ compress (ScalarWide.Ready g) (ready_of_frame g)
    hcompress hreduce

/-- Composition through the concrete linked reducer's one remaining exact
execution obligation. -/
theorem linked_finalizer_of_execution (compress : Compression)
    (call : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (g : ScalarWide.Globals) (hcompress : OneBlockCompressContract call compress)
    (hexec : ScalarWide.ExecutionObligation g) :
    ScalarFromSha512ContractUnder (ScalarWide.Ready g)
      (ScalarWide.finalizationPrimitives g call |> program).call (model compress) :=
  linked_finalizer_contract compress call g hcompress (linkedReduceWide_of_execution g hexec)

end Agave.Ed25519.Verifier.Execution.SHA512Finalization

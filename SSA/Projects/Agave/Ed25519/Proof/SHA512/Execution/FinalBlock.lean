import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.SerializationMemory
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.FinalTail

/-! The actual complete finalizer bb3, with only the invocation-local wide
scalar reduction contract left as an external premise. -/
namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Challenge
open Agave.Ed25519.SHA512

set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

/-- Serialization, the exact reducer call, every zeroizing store and fence,
and the final return. The frame equation keeps private writes explicit. -/
theorem final_block_of_contract (p : Primitives) (ready : GlobalState → Pointer → Prop)
    (hreduce : ReduceWideContractUnder ready p.reduceWide)
    (E : Env program.Γ) (s : GlobalState) (ctx digest out : Pointer)
    (scratch : Fin 64 → Pointer) (mark : Nat)
    (hctx : E.read (%86) = .value ctx)
    (hchain : E.read (%151) = .value (ctx.add 128#64))
    (hcount : E.read (%152) = .value (ctx.add 127#64))
    (hdigest : E.read (%85) = .value digest) (hout : E.read (%arg0) = .value out)
    (hzero : E.read (%8) = .value 0#8)
    (hscratch : ∀ i, E.read (scratchReg i) = .value (scratch i))
    (hwf : s.WF) (hc : SmallRange s.mem ctx 208) (hd : SmallRange s.mem digest 64)
    (ho : SmallRange s.mem out 32) (hs : ∀ i, SmallRange s.mem (scratch i) 1)
    (hdisjoint : (Range.of out 256).Disjoint (Range.of digest 512))
    (hready : ready (serializedState s ctx digest) out)
    (hcInternal : mark ≤ ctx.id.id) (hdInternal : mark ≤ digest.id.id)
    (hsInternal : ∀ i, mark ≤ (scratch i).id.id) :
    ∃ after,
      (program p).runFrom E 3 s = .value (.nil, after) ∧
      after.mem.eraseFrom mark =
        (s.mem.eraseFrom mark).storeAt out
          (digestScalarBytes (serialize (s.mem.readAt (ctx.add 128#64) 512))) ∧
      s.alloc.nextFreeBlock ≤ after.alloc.nextFreeBlock ∧ after.WF := by
  let S := serializedState s ctx digest
  let F := serializedEnv E s ctx digest
  have hsf : S.WF := writeWords_wf (clearCount s ctx) digest (chainWord s ctx) 8 hwf.storeAt
  have hsOut : SmallRange S.mem out 32 := writeWords_live _ _ _ _ _ _ (ho.storeAt _ _)
  have hsDigest : SmallRange S.mem digest 64 := writeWords_live _ _ _ _ _ _ (hd.storeAt _ _)
  have hsScratch (i : Fin 64) : SmallRange S.mem (scratch i) 1 :=
    writeWords_live _ _ _ _ _ _ ((hs i).storeAt _ _)
  have hfOut : F.read (%arg0) = .value out := by simpa [F, serializedEnv, mlir_env] using hout
  have hfDigest : F.read (%85) = .value digest := by simpa [F, serializedEnv, mlir_env] using hdigest
  obtain ⟨middle, hcall, heffect⟩ := hreduce S out digest hsf hready hsOut hsDigest hdisjoint
  have hmiddle : middle.WF := heffect.wellFormed hsf
  have hmDigest : SmallRange middle.mem digest 64 := heffect.smallRange hsDigest
  have hmScratch (i : Fin 64) : SmallRange middle.mem (scratch i) 1 :=
    heffect.smallRange (hsScratch i)
  have hfScratch : ∀ i, F.read (scratchReg i) = .value (scratch i) := by
    intro i
    have h := hscratch i
    fin_cases i <;> simpa [F, serializedEnv, scratchReg, mlir_env] using h
  have htail := final_tail p F middle digest scratch
    (by simpa [F, serializedEnv, mlir_env] using hzero) hfDigest
    (by simp [F, serializedEnv, mlir_env]) (by simp [F, serializedEnv, mlir_env])
    (by simp [F, serializedEnv, mlir_env]) (by simp [F, serializedEnv, mlir_env])
    (by simp [F, serializedEnv, mlir_env]) (by simp [F, serializedEnv, mlir_env])
    (by simp [F, serializedEnv, mlir_env]) hfScratch hmDigest hmScratch
  have hbody : (program.bb3 p).runBodyFrom E 0 s =
      .value (zeroizedEnv F digest, zeroizedState middle digest scratch) := by
    rw [runBodyFrom_slice (program.bb3 p) E F s S 0 42
      (by simpa using serialization_prefix p E s ctx digest hctx hchain hcount hdigest hzero hc hd)]
    rw [runBodyFrom_slice (program.bb3 p) F F S middle 42 1
      (reduce_slice p F S middle out digest hfOut hfDigest hcall)]
    exact htail
  have hblock : (program.bb3 p).run program.blockParams E s =
      .value ((zeroizedEnv F digest, .inl .nil), zeroizedState middle digest scratch) := by
    rw [BasicBlock.run_eq]
    simp only [EffectM.bind_eq, hbody, PoisonOr.value_bind]
    simp [EffectM.bind_eq, hbody, program.bb3, Exit.run, Regs.read_nil, EffectM.pure_eq]
  refine ⟨zeroizedState middle digest scratch, ?_, ?_, ?_, zeroizedState_wf _ _ _ hmiddle⟩
  · rw [Func.runFrom_eq]
    change ((program.bb3 p).run program.blockParams E s >>= fun x =>
      (program p).continue x.1.1 x.1.2 x.2) = _
    rw [hblock]
    rfl
  · rw [zeroizedState_frame _ _ _ _ hdInternal hsInternal, heffect.memory,
      MemoryState.eraseFrom_storeAt, serializedState_frame _ _ _ _ hcInternal hdInternal,
      serialized_readback s ctx digest hc hd]
  · simpa [S, serializedState] using heffect.counter

end Agave.Ed25519.Verifier.Execution.SHA512Finalization

import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.ContextContracts

namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Challenge

set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

/-- Compose an exact instruction slice with the remaining original body. -/
theorem runBodyFrom_slice (block : BasicBlock Γ rets bp) (E E' : Env Γ)
    (s s' : GlobalState) (start count : Nat)
    (h : (List.foldlM Instr.run E ((block.body.drop start).take count) : EffectM (Env Γ)) s =
      .value (E', s')) :
    block.runBodyFrom E start s = block.runBodyFrom E' (start + count) s' := by
  have hsplit : block.body.drop start =
      (block.body.drop start).take count ++ block.body.drop (start + count) := by
    simpa only [List.drop_drop, Nat.add_comm] using
      (List.take_append_drop count (block.body.drop start)).symm
  unfold BasicBlock.runBodyFrom
  conv_lhs => rw [hsplit, List.foldlM_append]
  simp only [EffectM.bind_eq, h, PoisonOr.value_bind]

/-- The reducer is invoked at instruction 42 of the actual bb3, with the
caller output pointer and serialized digest pointer, in that order. -/
theorem reduce_slice (p : Primitives) (E : Env program.Γ) (s after : GlobalState)
    (out digest : Pointer) (hout : E.read (%arg0) = .value out)
    (hdigest : E.read (%85) = .value digest)
    (hcall : p.reduceWide (.cons (.value out) (.cons (.value digest) .nil)) s =
      .value (.nil, after)) :
    (List.foldlM Instr.run E (((program.bb3 p).body.drop 42).take 1) :
      EffectM (Env program.Γ)) s = .value (E, after) := by
  change E.args 0 = .value out at hout
  simp [program.bb3, List.foldlM_cons, List.foldlM_nil, Instr.run,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
    Regs.read_cons, Regs.read_nil, Env.writeMany_nil, hout, hdigest, hcall]

/-- Discharge that single call cutpoint under an explicit state/global
invariant. No correctness premise about the whole finalizer is introduced. -/
theorem reduce_slice_of_contract (p : Primitives)
    (ready : GlobalState → Pointer → Prop)
    (hreduce : ReduceWideContractUnder ready p.reduceWide)
    (E : Env program.Γ) (s : GlobalState) (out digest : Pointer)
    (hout : E.read (%arg0) = .value out) (hdigest : E.read (%85) = .value digest)
    (hwf : s.WF) (hready : ready s out)
    (ho : SmallRange s.mem out 32) (hd : SmallRange s.mem digest 64)
    (hne : (Range.of out 256).Disjoint (Range.of digest 512)) :
    ∃ after,
      (program.bb3 p).runBodyFrom E 42 s = (program.bb3 p).runBodyFrom E 43 after ∧
      StoreEffect s after out (digestScalarBytes (s.mem.readAt digest 512)) := by
  obtain ⟨after, hcall, heffect⟩ := hreduce s out digest hwf hready ho hd hne
  exact ⟨after, runBodyFrom_slice (program.bb3 p) E E s after 42 1
    (reduce_slice p E s after out digest hout hdigest hcall), heffect⟩

end Agave.Ed25519.Verifier.Execution.SHA512Finalization

import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionProgram
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionState
import SSA.Projects.RIR.Run.Tactic

/-! The actual final block of the extracted challenge, including its entire
208-byte context copy and scalar-reduction call. The preceding seven blocks
must establish the explicit `ContextRepresents` memory invariant. -/

namespace Agave.Ed25519.Verifier.Execution.Challenge

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge Agave.Ed25519.Bridge.Challenge

/-- Execute the exact generated final block using a single primitive-call
equation. The memory copy and both lifetime markers are proved here. -/
theorem final_block (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state after : GlobalState) (dst src copy : Pointer)
    (hdst : E.read (%arg0) = .value dst)
    (hsrc : E.read (%18) = .value src) (hcopy : E.read (%19) = .value copy)
    (hlen : E.read (%16) = .value (208 : BitVec 64))
    (hsrcFits : Fits state.mem src 1664) (hcopyFits : Fits state.mem copy 1664)
    (hdisjoint : (Range.of copy 1664).Disjoint (Range.of src 1664))
    (hcall : p.scalarFromSha512 (.cons (.value dst) (.cons (.value copy) .nil))
      {state with mem := state.mem.storeAt copy (state.mem.readAt src 1664)} =
      .value (.nil, after)) :
    (program p g).runFrom E 7 state = .value (.nil, after) := by
  have hmemcpy : Operation.memcpy (.value copy) (.value src) (.value 208#64) E state =
      .value (E, {state with mem := state.mem.storeAt copy (state.mem.readAt src 1664)}) :=
    run_memcpy (env := E) (s := state) (dst := copy) (src := src)
      (len := 208#64) (n := 208) rfl hdisjoint hcopyFits hsrcFits
  have harg : E.args 0 = .value dst := hdst
  have hblock : (program.bb7 p).run program.blockParams E state =
      .value ((E, .inl .nil), after) := by
    simp [BasicBlock.run, program.bb7, List.foldlM_cons, List.foldlM_nil, Instr.run,
      EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
      mlir_env, Exit.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
      harg, hsrc, hcopy, hlen, hmemcpy, hcall]
  rw [Func.runFrom_eq]
  change ((program.bb7 p).run program.blockParams E state >>= fun x =>
    (program p g).continue x.1.1 x.1.2 x.2) = _
  rw [hblock]
  rfl

/-- The final block has no whole-program equality premise. Its only external
assumption is the scalar callee contract, including SHA finalization/padding
and digest reduction. All context-copy behavior is discharged by the actual
block execution and the byte-subrange preservation theorem. -/
theorem final_block_of_contract (p : Primitives) (g : Globals) (sha : Sha512Model)
    (hscalar : ScalarFromSha512Contract p.scalarFromSha512 sha)
    (E : Env program.Γ) (state : GlobalState) (dst src copy : Pointer)
    (completed pending : Bytes)
    (hdst : E.read (%arg0) = .value dst)
    (hsrc : E.read (%18) = .value src) (hcopy : E.read (%19) = .value copy)
    (hlen : E.read (%16) = .value (208 : BitVec 64))
    (hwf : state.WF) (hout : SmallRange state.mem dst 32)
    (hctx : ContextRepresents sha state.mem src completed pending)
    (hcopyLive : SmallRange state.mem copy 208)
    (hcopyDisjoint : (Range.of copy 1664).Disjoint (Range.of src 1664))
    (houtDisjoint : (Range.of dst 256).Disjoint (Range.of copy 1664)) :
    ∃ after,
      (program p g).runFrom E 7 state = .value (.nil, after) ∧
      (after.mem.readAt dst 256).toNat =
        (sha.digest (completed ++ pending)).toNat % subgroupOrder ∧ after.WF := by
  let copied : GlobalState :=
    {state with mem := state.mem.storeAt copy (state.mem.readAt src 1664)}
  have hcopied : ContextRepresents sha copied.mem copy completed pending :=
    ContextRepresents.copy sha state.mem src copy completed pending hctx hcopyLive
  obtain ⟨after, hc, houtcome, hwfAfter⟩ := scalar_contract_output
    p.scalarFromSha512 sha hscalar copied dst copy completed pending
    (GlobalState.WF.storeAt hwf) (hout.storeAt _ _) hcopied houtDisjoint
  refine ⟨after, ?_, houtcome, hwfAfter⟩
  exact final_block p g E state after dst src copy hdst hsrc hcopy hlen
    hctx.live.fits hcopyLive.fits hcopyDisjoint hc

end Agave.Ed25519.Verifier.Execution.Challenge

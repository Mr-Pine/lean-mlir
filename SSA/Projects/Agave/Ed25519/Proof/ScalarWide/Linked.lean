import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.ExecutionProgram
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Contract
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.BlackBoxProgram
import SSA.Projects.Agave.Ed25519.Proof.SHA512.ExecutionProgram
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionState

/-! Bind the extracted wide reducer to its actual Montgomery callee and the
already extracted byte black-box body. This is linkage, not an execution proof.
In particular, the contract below remains an explicit unproved proposition. -/

namespace Agave.Ed25519.Verifier.Execution.ScalarWide

open LeanMLIR.RIR
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Reduce64.Execution (SmallRange)
open Agave.Ed25519.Verifier.Execution.Dalek (args2 ReadBytes OutputFrame)

noncomputable def montgomeryPrimitives : ScalarMontgomeryMul.Primitives :=
  ⟨Agave.Ed25519.Encoding.Decompress.Execution.BlackBox.program.call⟩

noncomputable def linkedPrimitives : Primitives :=
  ⟨(ScalarMontgomeryMul.program montgomeryPrimitives).call,
    Agave.Ed25519.Encoding.Decompress.Execution.BlackBox.program.call⟩

/-- Bind all nonintrinsic callees to exact extracted bodies. The two constant
addresses remain explicit parameters, with their contents checked by `Ready`. -/
noncomputable def linkedProgram (g : Globals) : Func := program linkedPrimitives g

/-- Exact initializer and provenance obligations for the two immutable LLVM
globals. Output separation prevents mutation of either constant. -/
def Ready (g : Globals) (state : GlobalState) (out : Pointer) : Prop :=
  g.address0 = montgomeryR.address g.address0.id ∧
  g.address1 = montgomeryRR.address g.address1.id ∧
  montgomeryR.Present g.address0.id state.mem ∧
  montgomeryRR.Present g.address1.id state.mem ∧
  g.address0.id ≠ g.address1.id ∧
  out.id ≠ g.address0.id ∧ out.id ≠ g.address1.id

/-- Exact post-call state required of the linked implementation. The imported
outer body allocates 24 objects, each of its two Montgomery calls allocates
nine plus one in black-box, and its own black-box allocates one: 45 in total.
Every private object is removed by the enclosing call frame. -/
def exactPostState (state : GlobalState) (out : Pointer) (bytes : BitVec 512) : GlobalState :=
  { alloc := ⟨state.alloc.nextFreeBlock + 45⟩,
    mem := state.mem.storeAt out (reducedBytes bytes) }

/-- The remaining exact RIR execution obligation. No theorem in this module
asserts it. In particular, the fixed post-state and complete frame erasure must
be derived from the actual memory phases; observation-only frames do not imply
this equation. All scalar arithmetic uses the subgroup order. -/
def ExecutionObligation (g : Globals) : Prop :=
  ∀ (out input : Pointer) (state : GlobalState) (bytes : BitVec 512),
    state.WF → Ready g state out →
    SmallRange state.mem out 32 → ReadBytes state input 64 bytes →
    (Range.of out 256).Disjoint (Range.of input 512) →
    (linkedProgram g).call (args2 out input) state =
      .value (.nil, exactPostState state out bytes)

/-- The exact post-state supplies the stronger store effect consumed by SHA. -/
theorem exactPostState_effect (state : GlobalState) (out : Pointer) (bytes : BitVec 512) :
    Challenge.StoreEffect state (exactPostState state out bytes) out (reducedBytes bytes) := by
  exact ⟨rfl, Nat.le_add_right _ _⟩

/-- The observation frame is a corollary of exact memory/counter behavior. -/
theorem exactPostState_outputFrame (state : GlobalState) (out : Pointer)
    (bytes : BitVec 512) (hwf : state.WF) :
    OutputFrame state (exactPostState state out bytes) out 32 := by
  refine ⟨(exactPostState_effect state out bytes).wellFormed hwf, ?_, ?_⟩
  · intro q count hq
    exact hq.storeAt out (reducedBytes bytes)
  · intro q width hd
    exact MemoryState.readAt_storeAt_disjoint hd.symm (reducedBytes bytes)

/-- Exact call results retain the previous 32-byte observation as a corollary.
The execution obligation is still an explicit premise, not a proved leaf. -/
theorem observations_of_exact_execution (g : Globals) (hexec : ExecutionObligation g)
    (out input : Pointer) (state : GlobalState) (bytes : BitVec 512)
    (hwf : state.WF) (hready : Ready g state out)
    (hout : SmallRange state.mem out 32) (hin : ReadBytes state input 64 bytes)
    (hd : (Range.of out 256).Disjoint (Range.of input 512)) :
    (linkedProgram g).call (args2 out input) state =
        .value (.nil, exactPostState state out bytes) ∧
      OutputFrame state (exactPostState state out bytes) out 32 ∧
      ReadBytes (exactPostState state out bytes) out 32 (reducedBytes bytes) := by
  refine ⟨hexec out input state bytes hwf hready hout hin hd,
    exactPostState_outputFrame state out bytes hwf, hout.storeAt out (reducedBytes bytes), ?_⟩
  exact MemoryState.readAt_storeAt_self hout.fits (reducedBytes bytes)

/-- Exact memory replacement preserves both initialized constants because
`Ready` separates their allocation ids from the output allocation. -/
theorem exactPostState_ready (g : Globals) (state : GlobalState)
    (out : Pointer) (bytes : BitVec 512) (h : Ready g state out) :
    Ready g (exactPostState state out bytes) out := by
  rcases h with ⟨h0, h1, hr, hrr, hdistinct, hout0, hout1⟩
  exact ⟨h0, h1, hr.storeAt hout0.symm, hrr.storeAt hout1.symm,
    hdistinct, hout0, hout1⟩

/-- Local SHA-consumer interface for an independently established exact
execution obligation. It additionally preserves the invocation's globals. -/
theorem store_effect_of_exact_execution (g : Globals) (hexec : ExecutionObligation g)
    (state : GlobalState) (out input : Pointer)
    (hwf : state.WF) (hready : Ready g state out)
    (hout : SmallRange state.mem out 32) (hin : SmallRange state.mem input 64)
    (hd : (Range.of out 256).Disjoint (Range.of input 512)) :
    ∃ after,
      (linkedProgram g).call (args2 out input) state = .value (.nil, after) ∧
      Challenge.StoreEffect state after out
        (Challenge.digestScalarBytes (state.mem.readAt input 512)) ∧
      Ready g after out := by
  let bytes := state.mem.readAt input 512
  refine ⟨exactPostState state out bytes,
    hexec out input state bytes hwf hready hout ⟨hin, rfl⟩ hd, ?_,
    exactPostState_ready g state out bytes hready⟩
  exact exactPostState_effect state out bytes

/-- Exact linkage at the symbol used by the imported SHA-512 finalizer. -/
noncomputable def finalizationPrimitives (g : Globals)
    (compress : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals [])) :
    SHA512Finalization.Primitives :=
  { sha512Compress := compress, reduceWide := (linkedProgram g).call }

@[simp] theorem finalization_reduceWide (g : Globals)
    (compress : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals [])) :
    (finalizationPrimitives g compress).reduceWide = (linkedProgram g).call := rfl

end Agave.Ed25519.Verifier.Execution.ScalarWide

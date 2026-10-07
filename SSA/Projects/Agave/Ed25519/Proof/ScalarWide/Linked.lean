import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.ExecutionProgram
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Contract
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.BlackBoxProgram
import SSA.Projects.Agave.Ed25519.Proof.SHA512.ExecutionProgram

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

/-- The remaining exact RIR execution obligation. No theorem in this module
asserts it: the Montgomery arithmetic and wrapper memory execution must both
be proved. The resulting bytes use the subgroup order, not the base field. -/
def ExecutionObligation (g : Globals) : Prop :=
  ∀ (out input : Pointer) (state : GlobalState) (bytes : BitVec 512),
    state.WF → Ready g state out →
    SmallRange state.mem out 32 → ReadBytes state input 64 bytes →
    (Range.of out 256).Disjoint (Range.of input 512) →
    ∃ after,
      (linkedProgram g).call (args2 out input) state = .value (.nil, after) ∧
      OutputFrame state after out 32 ∧ ReadBytes after out 32 (reducedBytes bytes)

/-- Exact linkage at the symbol used by the imported SHA-512 finalizer. -/
noncomputable def finalizationPrimitives (g : Globals)
    (compress : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals [])) :
    SHA512Finalization.Primitives :=
  { sha512Compress := compress, reduceWide := (linkedProgram g).call }

@[simp] theorem finalization_reduceWide (g : Globals)
    (compress : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals [])) :
    (finalizationPrimitives g compress).reduceWide = (linkedProgram g).call := rfl

end Agave.Ed25519.Verifier.Execution.ScalarWide

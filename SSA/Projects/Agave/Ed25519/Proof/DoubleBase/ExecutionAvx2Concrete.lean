import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2LiveArithmetic
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorContract

/-! Concrete whole-backend and Dalek contracts. All helper bodies and all
arithmetic blocks are linked; readiness only names the actual base global. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR PointArithmetic
open Conformance.BackendExecution (Invocation readPoint RefinesAt)
open Verifier Verifier.Execution
set_option maxRecDepth 10000

noncomputable def concretePrimitives
    (panic : Vals [.bv 64, .bv 64, .ptr] → EffectM (Vals [])) : Avx2CFG.Primitives :=
  linkedArithmetic (Tables.Avx2Constructor.kernel Tables.Avx2Constructor.Double.actual).call panic

/-- The exact imported function refines double-base arithmetic from its live
caller objects and the actual immutable basepoint table. -/
theorem concrete_backend_refines
    (panic : Vals [.bv 64, .bv 64, .ptr] → EffectM (Vals []))
    (g : Avx2CFG.Globals) (i : Conformance.BackendExecution.Invocation) (initial : GlobalState)
    (hinput : Input i initial) (hglobal : GlobalsReady g initial) :
    RefinesAt (avx2Kernel (concretePrimitives panic) g).call avx2Math i initial :=
  backend_refines_of_local_blocks _ g
    (Tables.Avx2Constructor.Contract.linked_contract panic) i initial hinput
    (LiveContext g i initial) (liveContext_stable g i initial)
    (liveArithmeticBlocks g i initial _ panic)
    (outputBlock_of_ready (fun _ _ h => ⟨h.framed.1.outputRegisters, h.framed.1.output⟩))
    (prefix_liveContext g i initial hinput hglobal)

/-- The concrete readiness condition contains no block contract, execution
predicate or arbitrary local-environment assumption. The Dalek contract itself
supplies the ordinary live input objects and tight valid-point bytes. -/
theorem concrete_doubleBaseContractUnder
    (panic : Vals [.bv 64, .bv 64, .ptr] → EffectM (Vals []))
    (g : Avx2CFG.Globals) (cofactor : ValidPoint → ValidPoint) :
    Dalek.DoubleBaseContractUnder (fun _ _ _ _ initial => GlobalsReady g initial)
      (avx2Kernel (concretePrimitives panic) g).call
      (ValidPoint.layout cofactor) ValidPoint.doubleBase := by
  apply doubleBaseContractUnder_of_local_blocks _ g cofactor _
    (Tables.Avx2Constructor.Contract.linked_contract panic) (fun i initial => LiveContext g i initial)
    (fun i initial => liveContext_stable g i initial)
    (fun _ _ _ _ h => h.framed)
  · intro i initial _ _
    exact liveArithmeticBlocks g i initial _ panic
  · intro i initial hglobal hinput
    exact prefix_liveContext g i initial hinput hglobal

end Agave.Ed25519.DoubleBase.ExecutionAvx2

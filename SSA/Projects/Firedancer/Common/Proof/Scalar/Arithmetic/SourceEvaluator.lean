import SSA.Projects.Firedancer.Common.Proof.Scalar.fd_curve25519_scalar_reduce

/-!
Expose the kernel-reducible witness constructed by the committed source proof.
The elaborator only copies subterms of the existing checked proof. The new
value and its `ScalarReduceBy` certificate are checked by Lean's kernel.
This avoids a noncomputable choice when checking a particular digest.
-/

namespace Firedancer.Common.ScalarArithmetic
open LeanMLIR SLLVM

open Lean Elab Term Meta in
private def sourceWitness : TermElabM (Expr × Expr) := do
  let ci ← getConstInfo ``scalarReduce_determined
  let some value := ci.value? (allowOpaque := true) | throwError "source proof has no body"
  let value ← whnf value
  unless value.isAppOf ``Exists.intro do
    throwError "source proof did not expose an existential witness: {value.getAppFn}"
  let args := value.getAppArgs
  pure (args[args.size - 2]!, args[args.size - 1]!)

open Lean Elab Term in
elab "firedancer_scalar_source_expression" : term => do
  return (← sourceWitness).1

open Lean Elab Term in
elab "firedancer_scalar_source_certificate" : term => do
  return (← sourceWitness).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The actual poison-aware arithmetic expression from the MLIR proof.
Unlike a `Classical.choose` adapter, this function can be reduced by the kernel. -/
noncomputable def sourceReduce : BitVec (64 * 8) → Option (Fin 4 → BitVec 64) :=
  firedancer_scalar_source_expression

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Its certificate still names the exact imported source CFG. -/
theorem sourceReduce_by : ScalarReduceBy sourceReduce :=
  firedancer_scalar_source_certificate

end Firedancer.Common.ScalarArithmetic

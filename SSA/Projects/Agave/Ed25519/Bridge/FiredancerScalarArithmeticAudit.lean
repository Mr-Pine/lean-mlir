import SSA.Projects.Agave.Ed25519.Bridge.FiredancerScalarCertificates
import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.SignedRadix

/-! Guard the actual proof closures. No arithmetic result or LLVM-safety
claim is assumed. The optional invocation adapter is audited separately. -/

/-- info: Firedancer scalar source evaluation, agreement, arithmetic leaves, and six canonical certificates use only standard foundations. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let foundations : List Name := [`propext, `Classical.choice, `Quot.sound]
  let targets : List Name := [
    ``Firedancer.Common.ScalarArithmetic.sourceReduce,
    ``Firedancer.Common.ScalarArithmetic.sourceReduce_by,
    ``Firedancer.Common.ScalarArithmetic.packed_eq_on_readable,
    ``Firedancer.Common.ScalarArithmetic.packed_eq,
    ``Firedancer.Common.ScalarArithmetic.foldCoefficients_exact,
    ``Firedancer.Common.ScalarArithmetic.fold_identity,
    ``Firedancer.Common.ScalarArithmetic.fold_preserves_residue,
    ``Firedancer.Common.ScalarArithmetic.centeredDigit_eq_mod,
    ``Firedancer.Common.ScalarArithmetic.centeredDigit_bounds,
    ``Firedancer.Common.ScalarArithmetic.centeredCarry_identity,
    ``Firedancer.Common.ScalarArithmetic.finalFold_identity,
    ``Firedancer.Common.ScalarArithmetic.finalFold_canonical,
    ``Agave.Ed25519.Bridge.FiredancerScalarCanonicalAt.returns,
    ``Agave.Ed25519.Bridge.FiredancerScalarCanonicalAt.value,
    ``Agave.Ed25519.Bridge.firedancerScalarCanonicalAt_run,
    ``Agave.Ed25519.Bridge.firedancerScalarCanonical_zero,
    ``Agave.Ed25519.Bridge.firedancerScalarCanonical_order_sub_one,
    ``Agave.Ed25519.Bridge.firedancerScalarCanonical_order,
    ``Agave.Ed25519.Bridge.firedancerScalarCanonical_order_add_one,
    ``Agave.Ed25519.Bridge.firedancerScalarCanonical_high_bit,
    ``Agave.Ed25519.Bridge.firedancerScalarCanonical_max]
  for target in targets do
    for dependency in (← collectAxioms target) do
      unless foundations.contains dependency do
        throwError "Uninventoried scalar arithmetic dependency of {target}: {dependency}"
  logInfo "Firedancer scalar source evaluation, agreement, arithmetic leaves, and six canonical certificates use only standard foundations."

import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.LinkedHelperContracts

/-- info: Serial residual point helpers use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.SerialPoint.Execution.cachedSubWordTrace_unsigned,
    ``Agave.Ed25519.SerialPoint.Execution.affineSubWordTrace_unsigned,
    ``Agave.Ed25519.SerialPoint.Execution.affineAddWordTrace_unsigned,
    ``Agave.Ed25519.SerialPoint.Execution.cached_sub_call,
    ``Agave.Ed25519.SerialPoint.Execution.affine_sub_call,
    ``Agave.Ed25519.SerialPoint.Execution.affine_add_call,
    ``Agave.Ed25519.SerialPoint.Execution.cached_sub_contract,
    ``Agave.Ed25519.SerialPoint.Execution.affine_sub_contract,
    ``Agave.Ed25519.SerialPoint.Execution.affine_add_contract,
    ``Agave.Ed25519.SerialPoint.Execution.cached_sub_represents,
    ``Agave.Ed25519.SerialPoint.Execution.affine_sub_represents,
    ``Agave.Ed25519.SerialPoint.Execution.affine_add_represents,
    ``Agave.Ed25519.DoubleBase.RIR.serialResidualPointContracts,
    ``Agave.Ed25519.DoubleBase.RIR.serialLinkedHelperContracts]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Serial residual point helpers use only standard Lean axioms."

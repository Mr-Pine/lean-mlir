import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressSqrt
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Guard the complete axiom closure of the square-root endpoints independently
of the point-encoding dependencies. Smaller closures are permitted; any
dependency outside Lean's three standard axioms is a compilation error.
The audit is an elaboration-time check, not an assumption in any theorem.
-/

/-- info: All 12 decompression square-root endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Encoding.Decompress.source_d_limbs,
    ``Agave.Ed25519.Encoding.Decompress.source_sqrtm1_limbs,
    ``Agave.Ed25519.Encoding.Decompress.pow22501_eq,
    ``Agave.Ed25519.Encoding.Decompress.powP58_eq,
    ``Agave.Ed25519.Encoding.Decompress.candidate_eq,
    ``Agave.Ed25519.Encoding.Decompress.correctedRoot_sq,
    ``Agave.Ed25519.Encoding.Decompress.sqrtRatio_success_iff,
    ``Agave.Ed25519.Encoding.Decompress.sqrtRatio_success_iff_root,
    ``Agave.Ed25519.Encoding.Decompress.sqrtRatio_root,
    ``Agave.Ed25519.Encoding.Decompress.sqrtRatio_even,
    ``Agave.Ed25519.Encoding.Decompress.sqrtRatio_zero_numerator,
    ``Agave.Ed25519.Encoding.Decompress.sqrtRatio_zero_denominator]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All 12 decompression square-root endpoints use only standard Lean axioms."

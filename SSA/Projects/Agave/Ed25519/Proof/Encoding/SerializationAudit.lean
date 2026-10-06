import SSA.Projects.Agave.Ed25519.Proof.Encoding.SplitRefinement
import SSA.Projects.Agave.Ed25519.Proof.Encoding.ToBytesRefinement
import SSA.Projects.Agave.Ed25519.Proof.Encoding.FromBytesExecution

/-! Guard the exact split/serialization observation endpoints and their
canonical-byte/affine-compression value refinements. No overflow flag,
limb-tightness, nonzero-x, or canonical-input assumption is introduced.
The pointer-based middle from_bytes observations and aggregate projective
point-compression wrapper remain outside these execution endpoints. -/

/-- info: All 29 serialization endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Encoding.split_observe0_refines,
    ``Agave.Ed25519.Encoding.split_observe1_refines,
    ``Agave.Ed25519.Encoding.split_observe2_refines,
    ``Agave.Ed25519.Encoding.split_observe3_refines,
    ``Agave.Ed25519.Encoding.split_observe4_refines,
    ``Agave.Ed25519.Encoding.split_observe5_refines,
    ``Agave.Ed25519.Encoding.split_observe6_refines,
    ``Agave.Ed25519.Encoding.split_observe7_refines,
    ``Agave.Ed25519.Encoding.split_observe8_refines,
    ``Agave.Ed25519.Encoding.split_observe9_refines,
    ``Agave.Ed25519.Encoding.split_observe10_refines,
    ``Agave.Ed25519.Encoding.split_observe11_refines,
    ``Agave.Ed25519.Encoding.split_observe12_refines,
    ``Agave.Ed25519.Encoding.split_observe13_refines,
    ``Agave.Ed25519.Encoding.split_observe14_refines,
    ``Agave.Ed25519.Encoding.split_observe15_refines,
    ``Agave.Ed25519.Encoding.split_observe16_refines,
    ``Agave.Ed25519.Encoding.split_observe17_refines,
    ``Agave.Ed25519.Encoding.split_observe18_refines,
    ``Agave.Ed25519.Encoding.split_observe19_refines,
    ``Agave.Ed25519.Encoding.to_bytes0_canonical_call,
    ``Agave.Ed25519.Encoding.to_bytes1_canonical_call,
    ``Agave.Ed25519.Encoding.to_bytes2_canonical_call,
    ``Agave.Ed25519.Encoding.to_bytes3_canonical_call,
    ``Agave.Ed25519.Encoding.machineBytes_eq_toBytes,
    ``Agave.Ed25519.Encoding.machineAffineBytes_eq_compress,
    ``Agave.Ed25519.Encoding.machineSplitAffineBytes_eq_compress,
    ``Agave.Ed25519.Encoding.RIR.from_bytes0_call,
    ``Agave.Ed25519.Encoding.RIR.from_bytes4_call]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All 29 serialization endpoints use only standard Lean axioms."

import SSA.Projects.Agave.Ed25519.Proof.Avx2PointDouble.CFGPhases

/-! Audit of point-double arithmetic and exact helper-independent instruction
slices. Full execution, including the two imported helper calls, is audited
separately by `CFGAudit`. -/

/-- info: AVX2 point-double independent phases use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Avx2PointDouble.prepareOperation_value,
    ``Agave.Ed25519.Avx2PointDouble.mixOperation_value,
    ``Agave.Ed25519.Avx2PointDouble.doublePoint_reduced,
    ``Agave.Ed25519.Avx2PointDouble.doublePoint_value,
    ``Agave.Ed25519.Avx2PointDouble.CFG.prepare_frame,
    ``Agave.Ed25519.Avx2PointDouble.CFG.prepare_slice,
    ``Agave.Ed25519.Avx2PointDouble.CFG.prepare_field,
    ``Agave.Ed25519.Avx2PointDouble.CFG.mix_frame,
    ``Agave.Ed25519.Avx2PointDouble.CFG.mix_slice,
    ``Agave.Ed25519.Avx2PointDouble.CFG.mix_network,
    ``Agave.Ed25519.Avx2PointDouble.CFG.mix_field,
    ``Agave.Ed25519.Avx2PointDouble.CFG.right_field,
    ``Agave.Ed25519.Avx2PointDouble.CFG.left_frame,
    ``Agave.Ed25519.Avx2PointDouble.CFG.left_slice,
    ``Agave.Ed25519.Avx2PointDouble.CFG.left_field,
    ``Agave.Ed25519.Avx2PointDouble.CFG.prepared_stores,
    ``Agave.Ed25519.Avx2PointDouble.CFG.right_stores,
    ``Agave.Ed25519.Avx2PointDouble.CFG.left_stores,
    ``Agave.Ed25519.Avx2PointDouble.CFG.loadResult_frame,
    ``Agave.Ed25519.Avx2PointDouble.CFG.loadResult_slice]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "AVX2 point-double independent phases use only standard Lean axioms."

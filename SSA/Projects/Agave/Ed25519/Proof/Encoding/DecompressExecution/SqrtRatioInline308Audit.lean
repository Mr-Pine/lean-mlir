import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline308Readback

/-- info: SqrtRatioInline308 endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308.segment,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308.result_frame,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308.result_flag,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308.result_negative_low,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308.result_negative_high,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308.result_negative_ptr,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308.result_wf,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308.result_alloc,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308.result_live,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308.result_read_ne,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308.result_public,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308.result_left,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308.result_right,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308.comparison]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "SqrtRatioInline308 endpoints use only standard Lean axioms."

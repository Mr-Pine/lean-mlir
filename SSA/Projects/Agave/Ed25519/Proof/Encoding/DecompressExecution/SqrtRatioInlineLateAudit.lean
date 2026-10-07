import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineLateReturn

/-! Strict transitive audit for every late-composition theorem. -/

/-- info: All 17 late sqrt endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.InlineLate.state947_scratch,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.InlineLate.state956_scratch,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.InlineLate.state1047_scratch,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.InlineLate.state947_words,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.InlineLate.state956_candidate,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.InlineLate.state956_replacement,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.InlineLate.state947_comparison,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.InlineLate.state1047_root,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.InlineLate.frame_slot_value,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.InlineLate.constants577,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.InlineLate.correction_frame,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.InlineLate.registers956,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.InlineLate.registers577,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.InlineLate.segment,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.InlineLate.reaches_output,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.InlineLate.resume,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.InlineLate.root_value]
  for endpoint in endpoints do
    let axioms ← Lean.collectAxioms endpoint
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {endpoint}"
  logInfo "All 17 late sqrt endpoints use only standard Lean axioms."

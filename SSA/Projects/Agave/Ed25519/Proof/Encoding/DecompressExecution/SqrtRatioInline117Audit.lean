import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline117

/-! Strict dependency audit for the exact 189-instruction first sqrt inline
serializer slice and its renaming, register, memory, and field interfaces. -/

/-- info: All 30 sqrt inline-117 endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Encoding.Decompress.Execution.SerializerRename.Names.project_read,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SerializerRename.Names.project_write,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SerializerRename.Renaming.list_run,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SerializerRename.Renaming.list_success,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SerializerRename.tail54,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.index_bound,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.index_injective,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.arg_disjoint,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.load_segment,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.load_constants,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.load_project_args,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.exact_tail,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.source_supported,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.writes_above,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.tail_writes_above,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.writes_within,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.register_frame,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.byte_names,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.segment,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.resume,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.result_alloc,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.result_wf,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.result_live,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.result_read,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.result_readLimbs,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.result_erase,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.result_byte,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.result_word,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.result_compare,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117.result_check]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All 30 sqrt inline-117 endpoints use only standard Lean axioms."

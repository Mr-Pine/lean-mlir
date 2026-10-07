import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.InitializerExecution
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerShaInitializerLink

/-! Audit the initializer-to-readiness and concrete-entry links, including
parameterized Firedancer SHA call preservation. Only standard Lean logical
foundations are admitted; signature-only SHA constants and their legacy
semantic axioms are forbidden in every checked theorem's closure. -/

/-- info: SHA initializer, concrete entry, and parameterized call links use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.extracted_k64_eq,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.compressionReady_of_source_initializers,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.installShaSource_wf,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.installShaSource_ready,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.installShaSource_cold_cache,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.ShaSourceReady.iv_standard,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.ShaSourceReady.iv_entry,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.ShaSourceReady.fresh_call,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.ShaSourceReady.after_call,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.ShaSourceReady.of_frame,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.installed_dispatch_entry,
    ``Agave.Ed25519.Verifier.Execution.Challenge.entry_block_of_source_ready,
    ``Agave.Ed25519.Bridge.firedancer_source_k64_eq,
    ``Agave.Ed25519.Bridge.firedancerK64_standard_of_loaded,
    ``Agave.Ed25519.Bridge.firedancerWithK64_holds,
    ``Agave.Ed25519.Bridge.firedancerWithK64_wf,
    ``Agave.Ed25519.Bridge.firedancer_loadedK64_fresh_ready,
    ``Agave.Ed25519.Bridge.firedancerGlobalsReady_of_source_k64,
    ``Agave.Ed25519.Bridge.firedancerShaAppendBy_source_iff,
    ``Agave.Ed25519.Bridge.firedancerShaFinishBy_source_iff,
    ``Agave.Ed25519.Bridge.firedancerShaInit_preserves_k64,
    ``Agave.Ed25519.Bridge.firedancerShaAppend_preserves_k64,
    ``Agave.Ed25519.Bridge.firedancerShaFinish_preserves_k64]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "SHA initializer, concrete entry, and parameterized call links use only standard Lean axioms."

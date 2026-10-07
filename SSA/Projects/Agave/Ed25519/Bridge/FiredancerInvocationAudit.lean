import SSA.Projects.Agave.Ed25519.Bridge.FiredancerInvocationChallenge

/-!
Pure preparation and deterministic adapters use only Lean's standard three
foundations. The execution endpoint additionally retains exactly the three
legacy SHA program constants already present in the committed source proof.
The SHA determinism axioms are deliberately excluded from both inventories.
-/

/-- info: Firedancer invocation preparation and deterministic adapters have only standard foundations; source execution retains exactly the three legacy SHA constants. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let foundations : List Name := [`propext, `Classical.choice, `Quot.sound]
  let legacy := foundations ++ [
    `Firedancer.Common.fd_sha512_init,
    `Firedancer.Common.fd_sha512_append,
    `Firedancer.Common.fd_sha512_fini]
  let pureTargets : List Name := [
    ``Agave.Ed25519.Bridge.firedancerSourceReduce_by,
    ``Agave.Ed25519.Bridge.firedancerSourceReduce_returns_iff_defined_call,
    ``Agave.Ed25519.Bridge.firedancerSourceReduce_value_of_call,
    ``Agave.Ed25519.Bridge.firedancerBaseTable_values,
    ``Agave.Ed25519.Bridge.firedancerBaseTable_holds_of_entries,
    ``Agave.Ed25519.Bridge.FiredancerInputReady.args,
    ``Agave.Ed25519.Bridge.firedancerFreshSha_live,
    ``Agave.Ed25519.Bridge.FiredancerGlobalsReady.referenceWithSha,
    ``Agave.Ed25519.Bridge.FiredancerGlobalsReady.shaConstantsWithSha,
    ``Agave.Ed25519.Bridge.FiredancerGlobalsReady.baseTableWithSha,
    ``Agave.Ed25519.Bridge.firedancerDigest_fresh,
    ``Agave.Ed25519.Bridge.firedancerChallenge_fresh,
    ``Agave.Ed25519.Bridge.firedancerChallenge_returns_iff]
  for target in pureTargets do
    for dependency in (← collectAxioms target) do
      unless foundations.contains dependency do
        throwError "Uninventoried preparation dependency of {target}: {dependency}"
  let adapterTargets : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerGlobalsReady.environment,
    ``Agave.Ed25519.Bridge.FiredancerProofInvocation.digest_eq_of_digestBy,
    ``Agave.Ed25519.Bridge.FiredancerProofInvocation.challenge_eq_of_digestBy,
    ``Agave.Ed25519.Bridge.FiredancerProofInvocation.challenge_eq_of_digestBy_local,
    ``Agave.Ed25519.Bridge.FiredancerProofInvocation.challenge_eq_of_stream,
    ``Agave.Ed25519.Bridge.FiredancerProofInvocation.ofReadyReturns,
    ``Agave.Ed25519.Bridge.FiredancerProofInvocation.ofReadyDigestBy,
    ``Agave.Ed25519.Bridge.FiredancerProofInvocation.ofReadyDigestBy_challenge,
    ``Agave.Ed25519.Bridge.FiredancerProofInvocation.ofReadyDigestBy_challenge_local]
  for target in adapterTargets do
    for dependency in (← collectAxioms target) do
      unless legacy.contains dependency do
        throwError "Uninventoried adapter dependency of {target}: {dependency}"
  let executionTargets : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerProofInvocation.ready_executionRefines_of_challenge,
    ``Agave.Ed25519.Bridge.FiredancerProofInvocation.ready_executionRefines_of_digestBy,
    ``Agave.Ed25519.Bridge.FiredancerProofInvocation.ready_executionRefines_of_digestBy_local]
  for target in executionTargets do
    let actual := (← collectAxioms target).toList
    unless actual.length == legacy.length && legacy.all actual.contains do
      throwError "Wrong source execution dependency inventory for {target}: {actual}"
  logInfo "Firedancer invocation preparation and deterministic adapters have only standard foundations; source execution retains exactly the three legacy SHA constants."

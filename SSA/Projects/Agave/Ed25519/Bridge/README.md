# Ed25519 implementation and acceptance bridge

The complete Agave RIR verifier is connected to the existing Firedancer
reference verifier with concrete source-linked SHA calls. The strongest
entry point is `CrossClientLoaded.runs` in [CrossClientLoaded.lean](CrossClientLoaded.lean).
It constructs both loaded environments and proves that both actual executions
return defined results for arbitrary key, signature, and message bytes.

The exact acceptance relation is:

```text
Agave accepts ↔ Firedancer succeeds ∧ CanonicalY R
```

`CanonicalY R` requires the low 255 bits of the signature's R encoding to be
below `2^255 - 19`. `CrossClientLoaded.runs_of_canonical` proves equal acceptance
when that condition holds. Agave compares the canonical computed encoding;
Firedancer compares decoded points. The specification-level witness in
`PolicyWitness.lean` supplies neither a signature for a real message nor a
SHA-512 preimage, so it is not evidence of a reachable acceptance divergence.

## Strongest endpoints

| Endpoint | Scope and assumptions |
| --- | --- |
| `CrossClientLoaded.runs` | Actual executions on arbitrary original bytes in explicit loaded memories. Assumes only the hardware instruction contract, external bcmp32 contract, and message length `< 2^63`. |
| `CrossClientLoaded.runs_of_canonical` | The same executions have equal acceptance when R is canonical. |
| `CrossClientReachableConcrete.observations` and `runs` | General caller-memory version: raw initialized constants/tables and ordinary live-memory conditions, hardware, and bcmp. All SHA calls and digest correctness are supplied internally. |
| `AgaveReady.call_strict_bcmp` | The actual Agave wrapper returns the mathematical strict-verification Boolean, including malformed-input rejection. |
| `RIRChallengeEquivalence.calls` | Actual Agave challenge execution and Firedancer RIR SHA transcript produce the same reduced challenge bytes. |

There is no decoder, backend, compression, hash-execution, digest-equality,
result-equality, or valid-signature premise in the strongest endpoints.
Serial and AVX2 double-base multiplication and both Agave SHA backends are
proved. The byte transcript is the original `R || publicKey || message`,
including any noncanonical input encoding; it is not reconstructed from
curve points. Source scalar reduction is proved modulo the subgroup order.

`AgaveReadyEnvironmentWitness*` constructs Agave's literal globals and arbitrary
caller buffers. `FiredancerFieldInitializer` proves the seven raw field
initializers' values and bounds, removing the semantic `RefWF` assumption.
`FiredancerEnvironmentWitness` constructs a simultaneous Firedancer environment
with those fields, the base table, SHA constants, and arbitrary input buffers.
`FiredancerEnvironmentReads` identifies the actual observed key/R/S/message
bytes, including after the fresh SHA allocation.

The bcmp contract requires a read-only 32-byte comparison that returns zero
exactly when the bytes agree. Hardware contracts describe state-preserving
CPUID/gated XGETBV and sequential atomic stores. Feature-detection accuracy is
unnecessary because both selected backends are proved. Panic handlers remain
arbitrary parameters, with no behavior assumption: the proved executions do
not reach them.

## Proof organization and validation

The mathematical policy bridge in `Encoding`, `SmallOrder`, `Acceptance`,
`Equivalence`, and `FiredancerSpec` reuses Firedancer's existing curve and group
proofs. It introduces no second curve model or group axioms.

The SHA directory proves the complete RIR transcript and independently proves
the SLLVM calls needed by the older verifier interpreter. `verifierTailCalls`
constructs the actual third-append/finalizer contracts from the proved prefix
and stream representation. Allocation independence relates equal context and
input bytes across different caller allocations; it is proved, not assumed.
The [SHA boundary document](FiredancerSHAExecution/SLLVMSourceBoundary.md)
describes the imported functions and extraction pin.

Earlier `CrossClient*` modules remain available as more general conditional
interfaces. Legacy adapters that use signature-only SHA declarations retain
separate axiom audits and are not the strongest result.

All strongest endpoints were kernel checked on the designated devbox using
Lean `nightly-2026-09-16`. Independent validation reconciled the exact
1,639-source loaded-audit closure and 1,644-source combined closure with the
supporting audits. Both loaded endpoints depend on exactly `propext`,
`Classical.choice`, and `Quot.sound`. See [ProofClosureLedger.md](ProofClosureLedger.md)
for validation evidence and commits.

## Interpretation boundary

The result concerns the imported RIR/SLLVM CFGs and returned acceptance.
Compiler correctness, correspondence to a complete native validator binary,
and native LLVM undef/poison refinement are not proved. RIR's initialized
allocation model still needs that separate refinement. Physical alignment,
alias metadata, volatile-event traces, concurrent atomics, timing, and
error-code equality are outside the observation. The source and initializedness
audits document those boundaries; passing the axiom audit does not remove them.

For a clean checkout with its locked dependencies, the final audit target is:

```sh
lake build SSA.Projects.Agave.Ed25519.Bridge.CrossClientLoadedAudit
```

Run heavy builds on the designated devbox. Reuse cached artifacts only with
matching source and dependency provenance, including the nested LeanMLIR
package's parser. Source consistency checks include:

```sh
python3 SSA/Projects/Agave/Ed25519/Bridge/FiredancerSHAExecution/import_sllvm.py --check
python3 SSA/Projects/Agave/Ed25519/Bridge/check_field_initializer.py
```

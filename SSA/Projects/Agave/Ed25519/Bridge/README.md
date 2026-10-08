# Ed25519 implementation and acceptance bridge

The Agave proof reaches the actual linked RIR verifier. The source-linked
Firedancer comparison still has four invocation-specific SHA call contracts
to discharge. See [ProofClosureLedger.md](ProofClosureLedger.md) for the
checked endpoints, remaining work, and validation status.

The exact acceptance relation is:

```text
Agave accepts ↔ Firedancer succeeds ∧ CanonicalY R
```

`CanonicalY R` requires the low 255 bits of the signature's R encoding to be
below `2^255 - 19`. On canonical R, the returned acceptance Booleans agree.
Unrestricted equivalence is not the proved policy: Agave compares the canonical
computed encoding, while Firedancer compares decoded points. The mathematical
witness in `PolicyWitness.lean` does not supply a signature for a real message
or a SHA-512 preimage.

## Current entry points

| Entry point | What it establishes |
| --- | --- |
| `AgaveReady.call_strict_bcmp` in `AgaveBcmpOnly.lean` | The concrete Agave wrapper returns the mathematical strict-verification Boolean, including malformed-input rejection. Its only external function is bcmp; other assumptions describe caller/global memory and hardware instruction behavior. |
| `CrossClientReachableRawLoaded.observations` | Actual Agave and source-linked Firedancer observations agree with the canonical-R mask, assuming four reachable Firedancer SHA tail contracts. Literal base-table bytes discharge the group-table interpretation premise. |
| `CrossClientReachableRawLoaded.runs` | Both executions return defined results with that same policy relation, under the same assumptions. |
| `FiredancerSHAExecution.TranscriptInvocation.fresh_correct` | The actual Firedancer RIR init/append-R/append-A/append-message/finalizer sequence computes the standard SHA-512 transcript digest in a fresh context. |
| `FiredancerSHAExecution.SLLVMSource.Core.executes` | The imported Firedancer SLLVM scalar compression core computes standard SHA-512 compression for any positive block count satisfying `Ready`, preserving all other caller-visible live memory. |

Agave's theorem supplies decoder execution, scalar reduction, point operations,
serial and AVX2 double-base execution, point compression, SHA dispatch and both
SHA backends. It does not assume a valid key, scalar, or signature. Ordinary
input and environment requirements include live buffers, ABI length bounds,
well-formed memory, initialized constant/table bytes, legal cache bytes, and
separation from mutable caches. The external bcmp contract says that a
32-byte comparison returns zero exactly when the bytes agree and preserves
caller memory. Hardware contracts describe state-preserving CPUID/gated XGETBV
and sequential atomic stores; correct feature detection is unnecessary because
both selected backends are proved.

The Firedancer endpoint uses the existing reference verifier and arithmetic
proof, with actual imported SHA CFGs from pinned revision
`292f89b338a634e23e9f45c3dfdd5383ddcae624`. The remaining SHA assumptions concern
only the three appends and finalization reached by this invocation. They are
not a whole-verifier execution premise. The separate RIR transcript theorem
does not automatically discharge contracts in the older SLLVM interpreter;
direct SLLVM append/finalizer proofs and their adapters are being completed.

## Mathematical and legacy modules

`Encoding.lean`, `SmallOrder.lean`, `Acceptance.lean`, `Equivalence.lean`, and
`FiredancerSpec.lean` establish the policy bridge over Firedancer's existing
`Edwards.Point Ed25519.curve` and proved group operations. They introduce no
second curve model or new group axioms.

Earlier `CrossClient*` modules retain more local contracts for modular use.
They are not the strongest endpoints. `CrossClientAgaveReady.lean` closes the
Agave side but retains more general Firedancer SHA contracts and an explicit
digest equation. The reachable source comparison narrows those obligations.
Legacy adapters that use the old signature-only `fd_sha512_init`,
`fd_sha512_append`, and `fd_sha512_fini` declarations have a separate axiom
audit; they must not be described as standard-foundation-only results.

## Interpretation boundary

These are theorems about the imported CFGs in the RIR and SLLVM interpreters.
Compiler correctness and a native LLVM refinement are not proved. In
particular, RIR's initialized allocation model needs a separate connection to
LLVM undef/poison; alignment, alias metadata, volatile events, and concurrent
atomic behavior are not established by the return-value theorem. The source
and initializedness audits document these boundaries. Error-code equality,
timing equality, and whole-validator behavior are outside the observation.

The strict audits admit only `propext`, `Classical.choice`, and `Quot.sound`
for the current clean endpoints. This checks their transitive logical
dependencies; it does not discharge assumptions or prove source extraction
correctness. Imported source consistency can be checked with:

```sh
python3 SSA/Projects/Agave/Ed25519/Bridge/FiredancerSHAExecution/import_sllvm.py --check
```

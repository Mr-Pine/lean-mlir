# Proof closure and validation status

Updated 2026-10-08. The Agave RIR verifier and source-linked Firedancer reference
verifier are now connected with all cryptographic and SHA execution premises
discharged. The returned policy is exactly Agave acceptance iff Firedancer
success and canonical R. This is an interpreter-level result; the external
interpretation boundaries below remain explicit.

## Final statements

`CrossClientLoaded.runs` proves defined executions in two explicitly constructed
loaded environments for every 256-bit key, 256-bit R, 256-bit S, and byte-list
message. Its only propositional premises are:

- `InstructionContracts hardware`: modeled CPUID/gated XGETBV state preservation
  and sequential atomic-store behavior.
- `CompareContract compareCall`: read-only bcmp32, zero exactly when bytes agree.
- `message.length < 2^63`: the current signed object-size bound.

`runs_of_canonical` additionally assumes `CanonicalY R` and concludes equal
acceptance. Panic handlers are unconstrained parameters, unreachable in these
executions. No input-validity, memory-readiness, table-value, cryptographic,
SHA-call, digest-equality, or output-equality hypothesis is supplied.

`CrossClientReachableConcrete.{observations, observations_of_canonical, runs}`
is the general-memory version. It takes well-formed caller memory, exact raw
initialized globals/table bytes, buffer ranges and allocation-size conditions,
and the same hardware/bcmp boundaries. `FiredancerFieldInitializer.Loaded.refWF`
derives the former semantic field-global predicate from seven literal
40-byte allocations plus ordinary WF and the raw base table.

## Checked proof components

| Component | Commit | Result |
| --- | --- | --- |
| Complete Agave wrapper | `703c97309` | Concrete decoder, scalar arithmetic, serial/AVX2 backend, SHA dispatch, and wrapper control flow. |
| Firedancer RIR SHA transcript | `43f5433c1` | Actual init/R/A/message/finalizer calls compute the standard transcript digest. |
| Firedancer SLLVM compression | `78bfe5c22` | Arbitrary positive block counts, standard compression, private-frame cleanup, caller memory frame. |
| Agave/FD RIR challenge comparison | `68014e504` | Actual challenge and transcript executions, common digest/reduced scalar bytes. |
| Loaded Agave environment | `35c1093cc` | Simultaneous literal globals and arbitrary caller buffers; actual loaded wrapper execution. |
| Firedancer raw fields/environment | `2396256e8`, `85798091b` | Kernel-certified literal field values/bounds, simultaneous raw environment, exact original input reads. |
| SLLVM append | `df3c5ec81` | First two 32-byte calls and arbitrary third append, exact memory effects and stream semantics. |
| SLLVM finalizer | `449d27b2b`, `da2ef2802` | Both padding branches, standard digest, return value/frame, append/finalizer composition. |
| Allocation-independent third append | `575998efc` | Identical context/message bytes imply the same output context across distinct allocations; supplies the reachable call contract. |
| Closed general-memory comparison | `988ce1b2c` | All SHA calls supplied internally; exact canonical-R observation mask and defined executions. |
| Closed explicit-memory comparison | `2dadab0b3` | Only hardware, bcmp, and message-size premises; canonical-R acceptance corollary. |

The finalizer's discarded context bytes are not observed by the comparison.
Its actual execution, returned output pointer, digest bytes, allocator/global
preservation, and relevant memory frame remain proved. Original R/public-key
bytes are hashed directly, including noncanonical encodings.

## Independent validation

Authentication was restored and all pending kernel checks completed on the
designated devbox on 2026-10-08. Lean is `nightly-2026-09-16` with locked
packages. The exact `CrossClientLoadedAudit` import closure has 1,639 repository
sources; the combined closure with supporting audits has 1,644. All are tracked
in the branch. Source hashes and resolved compiled artifact hashes match the
validated snapshots. Both final loaded endpoints have exactly the three
standard dependencies `propext`, `Classical.choice`, and `Quot.sound`; strict
allowlist audits and an independent exact-set check passed.

Validation reused hash-verified prior builds and independently replayed missing
or changed dependencies, rather than claiming an entirely fresh checkout build.
This included 77 previously unreplayed comparison dependencies, 37 SHA proof
dependencies, four new allocation-adapter modules, seven final-composition
modules, six supplementary SHA composition/audit roots, and the new environment,
read, and loaded-comparison roots. The previous 312-module challenge replay was
recovered and verified; both challenge roots passed again.

The stale-parser issue was resolved by verifying the actual nested package
lookup path. Correct `GenericParser.olean` SHA-256:
`2273a69d3253227afbbde2c32baef618f29a5694d5a41318a722d5f73c6a5b5b`.
Lake searches `LeanMLIR/.lake/build/lib/lean` before the root artifact directory;
copying a corrected parser only into the root directory is insufficient.

Committed validation manifests (historical devbox evidence):

| Manifest | SHA-256 |
| --- | --- |
| `CrossClientLoaded-manifest.json` | `b2a4ce1165f5a88ac41b5374bfd64d46de683886e72cbd7fdeebddccbc986079` |
| `CrossClientReachableConcrete-manifest.json` | `318953eacc9f95cb27a2fd2de832751e51274e1eba6deb2901196f5b0c94d963` |
| `RIRChallengeEquivalence-manifest.json` | `85903732b495e293a2086191ef929c80d4be9c30b4f430faec88d4c3a3c68d7d` |
| `AgaveReadyEnvironmentWitness-manifest.json` | `085627f371922acd6503151e0215e16958a5b2e9fb65431e536c9f5ea484855f` |

These records were retained when importing the completed proof history onto
`agave-ed25519-rir` in the main repository. All 1,644 recorded repository source
hashes and the three toolchain/configuration hashes match the packaged files.
Absolute paths in the records identify the original validation environment;
they are not required checkout locations. Packaging did not rerun the Lean
build or change any proof source. The existing `agave-lthash` branch is separate
and unchanged; this branch retains the proof's RIR framework ancestry.

The independent mirror is `/tmp/lmf-crossclient-final-independent-20261008` on
`liam@htz-hel1-seceng-dev-liam1.nodes.asymmetric.re`. Manifests contain commands,
source/artifact hashes, audit results, and supporting evidence hashes. The
pinned SHA importer and seven-field initializer checker both passed.

## Remaining interpretation boundaries

The theorem compares the imported Agave RIR implementation and the existing
Firedancer reference CFG linked to independently proved scalar SHA regions.
It does not prove compiler correctness, equivalence to a full native validator
binary, or a source-version identity for the older unpinned verifier lift.
The newer SHA/field initializer source pin is
`292f89b338a634e23e9f45c3dfdd5383ddcae624`.

External bcmp and hardware behavior remain ABI/model contracts. Native LLVM
undef/poison refinement, physical alignment, alias metadata, volatile-event
traces, concurrency, timing, and error-code equality remain outside the theorem.
The initializedness and source-memory audits document those separate issues.
The noncanonical-R policy witness supplies no real-message signature/preimage,
so the result does not establish a reachable acceptance divergence.

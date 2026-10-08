# Proof closure and validation status

Updated 2026-10-08. The complete Agave RIR wrapper proof is committed. The
strongest source-linked cross-client theorem still assumes four reachable
Firedancer SHA tail contracts. Full cross-client implementation closure has
not yet been claimed.

## Checked work

| Scope | Endpoint / audit | Status |
| --- | --- | --- |
| Full Agave wrapper | `AgaveReady.call_strict`, `AgaveReady.call_strict_bcmp`; `AgaveReadyExecutionAudit` | Previously kernel checked and independently reviewed; committed in `703c97309`. No decoder, backend, SHA, prefix, or whole-execution premise remains. |
| Firedancer RIR SHA transcript | `TranscriptInvocation.execution`, `correct`, `fresh_correct`; `TranscriptCorrectAudit` | Previously checked with the 204-module source closure and 42 audit endpoints; committed in `43f5433c1`. |
| Imported SLLVM SHA init | `SLLVMSource.init_contract`, `reachableInit` | Previously checked; committed in `e3e51f6b0` and `86885b656`. |
| Imported SLLVM SHA compression | `SLLVMSource.Core.executes`; `SLLVMSourceCoreAudit` | Saved successful devbox check from 2026-10-07; source review and all 194 local source hashes rechecked on 2026-10-08. Committed in `78bfe5c22`. |
| Reachable source-linked comparison | `CrossClientReachableRawLoaded.observations`, `observations_of_canonical`, `runs`; `CrossClientReachableSourceAudit` | Saved successful devbox check from 2026-10-07; all 1,524 local source hashes rechecked on 2026-10-08. Committed in `bc27d794d`, following contract adjustment `374e78308`. Four SHA tail contracts remain. |

The core theorem accepts well-formed memory; live chain, input, and K-table
ranges in allocations smaller than `2^63` bytes; a positive block count; exact
K bytes at the named global; and separation of the chain from constants and
input. It concludes actual execution, the standard compression result,
restored allocation/global state, and a complete live-memory frame. It has no
execution or output-equality premise.

The reachable comparison derives the fixed base-table semantics from exact
pinned table bytes. Its SHA loader supplies exact named 640-byte global
storage; the remaining tail contracts must instantiate those bytes with the
standard constants. The last SHA context allocation is discarded by the
verifier, so its exact post-finalization contents are no longer part of the
contract. Actual finalizer execution, digest output, and relevant memory
framing remain required.

## Work awaiting validation or integration

These working-tree modules are not included in the checked table above.

| Work | Current boundary |
| --- | --- |
| `SLLVMAppend*` and `SLLVMAppendMessage*` | Source proofs cover the first two appends and the arbitrary-message append after 64 pending bytes, using `Core.executes`. Recheck their saved devbox build state before treating the complete closure as validated. |
| `SLLVMFinish*` | Source proofs cover both padding branches and the digest relation, with `SLLVMSource.FinishCorrect.call_digest_source` supplying the concrete core. Complete-closure validation remains to be recovered or rerun. |
| `SLLVMAppendFinish` and audit | New, uncompiled composition of actual message append and finalization for the R/A/message transcript. |
| `FiredancerReachableSourcePrefix`, `CrossClientReachablePrefix`, and audit | New, uncompiled adapters discharging the first two reachable append contracts for the verifier's actual initial context. The new cross-client endpoint retains third-append and finish contracts. |
| `AgaveReadyEnvironmentWitness*` | Explicit literal globals and arbitrary caller buffers witness simultaneous memory readiness. New `call_strict_loaded` instantiates the concrete wrapper with only hardware, bcmp, and message-length assumptions. Source reviewed; not newly kernel checked. |
| `RIRChallengeEquivalence` and audit | Individual roots previously passed. Completion of the subsequent full dependency rebuild remains unconfirmed. This composes actual Agave challenge execution with the Firedancer RIR transcript and source scalar reduction; it is not an RIR/SLLVM simulation. |

The remaining composition problem is an allocation-independence lemma for
`SLLVMSource.MessageExecution.resultState`. Given equal incoming context
blocks at equal offsets, equal bounded message bytes, live small ranges, and
context/message separation in both states, the resulting context blocks must
be equal. The addresses and unrelated memory may differ. Existing congruence
under whole-state equivalence is insufficient for this interface.

The proof can proceed by transporting bounded input slices and context
reads/stores, then splitting the message-length branches: zero, below 64,
exactly 64, below 192, and at least 192 bytes. Each core result is a pure
`SHA512.Spec.run` over equal chaining words and input slices. A canonical
context/message allocation then determines the fixed resulting `LiveBlock`
required by `FiredancerReachableAppend`. Link the R/A prefix to
`ContextRepresents`, and use the resulting stream representation with the
existing finalizer theorem. These are remaining proof obligations, not
assumptions added to a supposedly closed endpoint.

After those adapters, instantiate the four reachable contracts with standard
K bytes and the standard transcript digest, then rebuild the final
cross-client theorem and strict audit. The theorem should retain the exact
canonical-R policy; the specification-level noncanonical-R witness does not
establish a real-message acceptance divergence.

## Rebuild requirements and retained evidence

No new Lean compilation ran on 2026-10-08. The required devbox's Teleport
profile had expired, so remote SSH authentication could not complete. Heavy
computation remains assigned to that devbox. Local `/tmp` validation evidence
from the previous session is gone, and local oleans are stale or incomplete.
They are not a replacement for the saved validation records.

The retained manifests are untracked working-tree evidence:

- `FiredancerSHAExecution/sllvm-core-manifest.json`: SHA-256
  `ba92b6bd925b6eb78dbe26554d7fe093fc22737d70507e807325a7a946d61800`.
  Its 19 target and 175 transitive source hashes, three toolchain/lock hashes,
  extraction manifest hash, and exact import-closure membership match.
- `CrossClientReachableSource-manifest.json`: records the 1,524-source closure
  and the final ten-module rebuild, including both audits. All listed source
  hashes match. This verifies source identity with the saved check, not a
  fresh kernel replay.

The prior build audit found a stale `GenericParser.olean`. The corrected
artifact SHA-256 is
`2273a69d3253227afbbde2c32baef618f29a5694d5a41318a722d5f73c6a5b5b`.
Lake searches the nested `LeanMLIR/.lake/build/lib/lean` before the root build
directory; replacing only the root copy leaves the stale parser active.
Rebuild affected dependents against the corrected nested package. The
challenge closure contains 865 local sources, 546 of them parser-affected;
completion of the previous 312-module additional replay must be verified.

Use the configured toolchain and locked packages on:

```sh
ssh -A liam@htz-hel1-seceng-dev-liam1.nodes.asymmetric.re
```

Compile dependencies in order and then their audits, using the devbox's
`/home/liam/.elan/bin/lake env lean -j1 --tstack=400000`. Record source and
artifact hashes together. The importer consistency check passed again on
2026-10-08 for all four pinned SLLVM SHA regions.

## Remaining external interpretation boundaries

The current Agave theorem requires an external read-only bcmp32 ABI contract,
state-preserving hardware instruction laws, and sequential atomic-store
semantics. Its environment premises describe exact initialized bytes and
ordinary caller memory; no valid-signature premise is required. Both scalar
and AVX2 backend paths are proved, so CPU feature-detection accuracy is not
assumed.

Theorems concern the imported interpreter semantics. Compiler correctness,
native LLVM undef/poison refinement, alignment/alias metadata, volatile-event
traces, and concurrent atomic behavior remain outside this proof. A strict
axiom audit checks logical dependencies, not these correspondence claims or
the satisfiability of a theorem's hypotheses.

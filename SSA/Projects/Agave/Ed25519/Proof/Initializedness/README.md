# Stack initializedness boundary audit

The current RIR verifier theorem is **not yet a theorem that LLVM stack initializedness is irrelevant on every verifier path**. A blanket requirement that every byte read by `memcpy` was previously written is false in the original Agave challenge. This audit preserves that source behavior, adds checked independence results at relevant cutpoints, and records the remaining source/RIR relation precisely. It introduces no hypothesis that all source stack allocations are zero-filled.

## Actual counterexample and why the tail is not observed

In [Verifier/ExecutionProgram.lean](../Verifier/ExecutionProgram.lean), `Challenge.program.bb0` allocates `%17 : [127 x i8]` at line 471. Instructions 24 and 28 write only `[0,32)` and `[32,64)`. Instruction 29, line 483, copies all 127 bytes to `%18`. Therefore offsets **64 through 126** are copied before being written on every challenge invocation. The original LLVM witness is `MLIR/generated/agave_verifier_challenge_scalar.ll`, lines 11–23. Three instruction-position equalities in [Observations.lean](Observations.lean) check this exact imported region; `challenge_tail_not_written` checks the uncovered interval.

The later 208-byte context copy at line 548, and the finalizer's `EntryTail.cloned`, can transport the same unused bytes again. For message length below 64, the pending prefix is `[0,64+|M|)`; the remaining bytes below 127 stay unused. For larger messages, the first 64 message bytes overwrite context offsets `[64,128)` before the first compression. Each subsequent remainder defines the new pending prefix. The computational context fields are the count byte at 127, chaining words at `[128,192)`, counter at `[192,208)`, and the pending prefix.

`ChallengeExecutionState.ContextRepresents` intentionally constrains only those meaningful fields. `PaddingMemory.padBuffer_bytes` quantifies arbitrary source and destination memories and reads only the pending prefix. The new `padding_ignores_unused_bytes` theorem proves that equal pending prefixes yield the same full 128-byte padding buffer even when source tails and old destination bytes differ. Thus the unused bytes are not an implicit zero-padding input at this proof cutpoint.

Pointer `noundef` attributes on a copy's arguments do not state that all pointee bytes were initialized. Conversely, equality for arbitrary stable concrete bytes alone is not a proof about LLVM `undef` or poison: `undef` can choose differently at different uses, and poison has propagation rules. See the official [LLVM undefined-behavior documentation](https://llvm.org/docs/UndefinedBehavior.html) and [language reference](https://llvm.org/docs/LangRef.html#poison-values).

## Exact semantic gap

`SSA/Projects/RIR/Semantics/Effectful/Memory/Operations.lean` defines `GlobalState.alloca` by inserting a zero-valued bitvector. Ordinary `Operation.load` in `Semantics/Operations/Memory.lean` checks pointer poison and `Fits`, then reads concrete bits; memory carries no initializedness mask. A store rejects a poisoned value and checks `Fits`, but does not record byte definedness. `memcpy` copies concrete bits. `Instr.eval` treats lifetime start/end as no-ops.

The remaining sufficient source-boundary obligation is a **byte-definedness shadow trace for the actual reachable execution and all its callees**, under defined caller inputs and immutable global constants:

1. Fresh allocation or a new lifetime starts with no defined bytes. Ending the lifetime invalidates the object.
2. A store of a defined value and a defined `memset` mark exactly their written range. `memcpy` transports the source mask to the destination; it need not require the whole source range to be defined.
3. Each ordinary computational load reads defined bytes. Addresses, lengths, branch conditions, assumptions and other scalar operands whose definedness the source requires are defined. A callee preserves this property and its returned values/output spans are defined wherever subsequently observed.
4. The final verifier Boolean and relevant returned output bytes are defined. Copied private padding that is never consumed by a computation may remain undefined.
5. A source/RIR simulation equates only defined bytes, preserves live objects and effects, and connects these source steps to the checked RIR execution. The source's other semantic preconditions remain separate obligations.

The smallest restriction established here is therefore on **computationally consumed bytes**, not on all allocated bytes or all bytes transported by a private copy. This audit does not claim the above obligations have been proved for every imported verifier callee. It does not discharge the existing endpoint's source-semantics boundary merely by changing its wording.

[ShadowTrace.lean](ShadowTrace.lean) makes the byte-memory part concrete. For a fixed list of allocation/lifetime resets, defined writes, copies and computational reads, `defined_trace_observations_equal` proves equal read observations from any two memories that agree on the initial defined mask, with arbitrarily different fresh-allocation contents. A copy propagates its mask. `DefinedTrace` requires every recorded computational read to be defined. This is an abstract trace theorem, **not** an extraction of the verifier's RIR trace, an LLVM interpreter, or a proof of equal control flow. The missing connection includes establishing defined scalar values/addresses, constructing the trace from every actual execution, and relating LLVM behavior to it.

## Scope and unresolved paths

[static-report.json](static-report.json) inventories all literal `execution_def` and `mlir_def` regions under `Agave/Ed25519`, including secondary backends and generated observation/audit regions. It records exact source SHA-256 values and the explicit requested roots. The roots include `CrossClientReadyUnderAudit`, `CrossClientGuardedCaller`, the pointwise digest/actual Firedancer verifier bridge, complete Agave SHA dispatch/finalization, decoder semantic/ready/sqrt bridge audits, and every current Firedancer SHA audit.

At this snapshot there are 62 source files, 105 literal regions, 69 regions in the selected roots' import closure, and **324 allocation sites**. All 324 occur in that import closure. Import reachability overapproximates execution reachability; the inventory is not a verified interprocedural call graph. The 29 allocation-bearing regions and their remaining boundaries are enumerated in [inventory.md](inventory.md).

The static pass converges on all regions. It covers 32 local read sites using preceding local writes, and leaves **357 read sites, 166 helper-call sites and 19 unknown-pointer read sites unresolved**. These are conservative candidates, not 542 bugs: the pass deliberately does not infer output initialization from `sret`, `readonly` or a function name, and kills local coverage when an unknown call receives the object. It cannot prove dynamic loop/index bounds or pointer block-argument aliases, and does not propagate scalar undef/poison. Even a locally covered read is evidence, not a Lean certificate.

The unresolved whole-verifier obligations affect decoder/sqrt/power composition, compression, both double-base backends and table constructors, serial point/small-order helpers, NAF loops, scalar wide reduction, verifier wrapper/key/Dalek result layouts, and finalization/reduction helper effects. `ScalarReduce32`, scalar Montgomery multiplication and black-box byte handling have no outstanding known-local-read candidate after local store coverage, but the static pass is not a full semantics proof for them. Helpers with no private allocations still require defined input spans and defined scalar/output effects at their call boundary. The exact source line, allocation register, range, callee and reason for each candidate are in the JSON report.

No ordinary computational read of unwritten bytes was found in the targeted challenge and Firedancer executions below, or in the reviewed AVX2 SHA initialization order. This does **not** settle all 357 residual read candidates in the remaining verifier graph.

## Checked and inspected SHA cutpoints

[FiredancerRing.lean](FiredancerRing.lean) proves `rounds_ignore_initial_ring`: two arbitrary initial memories with equal message bytes and the required constant table execute the actual eighty imported round blocks to the same final working state, without a premise about the original 128-byte ring contents. It uses `CoreEightyRounds.eighty_from_input`, which establishes the first sixteen words by stores before later ring reads. `initialRingMemory_zero` is the vacuous zero-written-prefix case, not an assertion that the allocator supplies zero bytes. This theorem concerns the existing concrete RIR semantics and carries the existing live-range, separation and entry-environment premises.

For the actual Agave AVX2 compressor, read-only source inspection found:

- Count one: `Avx2Program.bb2` initializes all eight 16-byte ring pairs at offsets 0 through 112 before its first ring load. The other two stack objects are not computationally read on this route. Count zero likewise does not read them.
- Bulk: `bb9` initializes the complete first-block ring and the first 128 bytes of the second-block schedule cache. The schedule loop fills all remaining cache pairs before the 80-word cache-read loop. Each outer iteration repeats initialization. There is no `memcpy` in this compressor region.
- Existing generic-memory theorems `Avx2ExecutionInitialBlock.initial_block_body`, `Avx2ExecutionInitialMemory.initialScratchStores_ready`, `Avx2ExecutionPairMemory.read_pair`, and `Avx2ExecutionCompressionPrivate.compression_from_pairs_private` do not require initial scratch bits. The analogous bulk APIs are `Avx2ExecutionBulkInitialLoad.bulk_initial_load_body`, `Avx2ExecutionBulkInitialLoadMemory.bulkInitialStores_scratch`/`bulkInitialStores_cache`, `Avx2ExecutionBulkPairMemory.BulkCachePrefix.advance`/`complete`, and `Avx2ExecutionBulkPairPrefix.bulk_prefix_sixtyfour`.

Those existing interfaces and source-order facts support the mask argument but are not themselves new initializedness-mask proofs. This audit's build does not independently rebuild the entire AVX2 bulk lane.

## Targeted execution and reproducibility

[targeted_checks.py](targeted_checks.py) is an independent, unverified interpreter for the actual scalar MLIR regions. It starts allocated bytes undefined, separately fills their concrete contents with `00`, `55`, `AA` or `FF`, propagates masks through copies, resets masks on lifetime start and checks computational loads. Unsupported opcodes fail. It does not independently check LLVM overflow or alignment promises.

The recorded tests in [targeted-report.json](targeted-report.json) are:

- 2,080 Agave challenge cases: message lengths 0–512 and 1023, 1024, 1025, 4095, 4096, 4097, 65535, for four fills. All three challenge CFG routes were exercised. One or three copies transport undefined tail bytes; no ordinary load does. Observed callback outputs are fill-independent. Compression is a boundary observer and the finalizer callback models the separately proved padding algorithm; this is not execution of the full actual Agave compressor/finalizer.
- 16 actual Firedancer core cases: one, two, three and five blocks, for four fills. No undefined read/copy and equal chaining outputs across fills.
- 1,052 complete actual Firedancer `Init`/`Append`/`Core`/`Finish` transcripts: `R || A || M`, lengths 0–257 and 1023, 1024, 1025, 4095, 4096, for four fills. All 80 rounds are interpreted on each block. Every digest equals Python `hashlib.sha512`; no read or copy encounters undefined bytes.

Run from the repository root:

```sh
python3 SSA/Projects/Agave/Ed25519/Proof/Initializedness/stack_audit.py
python3 SSA/Projects/Agave/Ed25519/Proof/Initializedness/targeted_checks.py
python3 SSA/Projects/Agave/Ed25519/Proof/Initializedness/validate.py
```

The last command builds only the four new Lean modules, in order, against already-built dependencies. [validation.json](validation.json) records commands, exit codes, elapsed times, source and olean hashes, and 153 repository source hashes in the import closure, including the new modules. All four modules exited zero on the devbox; [Audit.lean](Audit.lean) restricts all ten new endpoints to `propext`, `Classical.choice` and `Quot.sound`. The imported source hashes matched the local checkout at freeze time. This is not a fresh rebuild of all imported dependency oleans. Static and targeted evidence remains separate from those checked theorems.

The same targeted script passed on the devbox with an identical JSON result. The remote static scan agrees on all 61 shared literal-program sources and every allocation/read/call count. That mirror lacks eight recently added root modules and the three non-production `SourceMemoryAudit/Translation` audit regions; therefore its import-reachability totals differ. The complete local root traversal and its 62-file snapshot are the authoritative scope inventory. [reproducibility.json](reproducibility.json) records this exact difference rather than presenting the remote scan as a complete rebuild of the current roots.

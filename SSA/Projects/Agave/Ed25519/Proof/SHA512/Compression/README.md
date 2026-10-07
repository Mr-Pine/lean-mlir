# SHA-512 compression implementation boundary

The existing padding development takes an abstract complete-block compression
operation. `../CompressionSpec.lean` supplies a separate FIPS 180-4 algorithm:
all eighty constants, big-endian input decoding, an append-only schedule,
eighty working-state rounds, and feed-forward. `../CompressionFold.lean`
connects that algorithm to the padding interface by block decomposition.
`ScheduleSpec`, `ScheduleArithmetic`, and `RotationArithmetic` provide reusable
schedule and round identities. `WindowSchedule` tracks all thirty-two AVX
two-word window updates; `RoundComposition` composes arbitrary short round
segments and the full eighty rounds. `InputByteOrder` connects the independent
big-endian decoder to RIR's exact scalar byte-swap operation. These sources
compile with the pinned Lean toolchain. `CompressionSpecAudit` checks their
transitive axiom closure against only `propext`, `Classical.choice`, and
`Quot.sound`; no native evaluation or SAT-check axiom is admitted. These pure
arithmetic results support the concrete scalar and AVX2 execution refinements
described below.

The dependency is the exact `sha2` 0.11.0 package pinned by
`MLIR/Cargo.extract.lock` (archive SHA-256
`446ba717509524cb3f22f17ecc096f10f4822d76ab5c0b9822c5f9c284e825f4`).
The full package is archived in `MLIR/source-sha2`; its file manifest is
`MLIR/sha2-source-manifest.json`. Both that archive and the registry directory
used by the original dependency build have been checked against the manifest.

The caller's external symbol is
`_RNvNtCs7dqAOVfn11v_4sha26sha51211compress512`. The original dependency was
compiled with no features and no extra rustflags. On x86-64 it dispatches at
runtime between `x86_avx2::compress` and the scalar `soft::unroll::compress`.
The software round body is inlined in the dispatcher by rustc. A one-block
AVX2 call follows the odd-block prologue and does not enter the two-block loop.

`MLIR/extract_sha512_compress.py` rebuilds only that locked dependency and
selects the original dispatcher and AVX2 function definitions. It applies no
Rust rewrites, observation wrappers, forced-backend configuration, or extra
LLVM inlining. It checks that the resulting dispatcher symbol is exactly the
symbol used by the already extracted scalar finalizer. Extraction has run:
the two complete LLVM/MLIR regions and the tool/source/fingerprint inventory
are under `MLIR/generated`. Both the extraction and quote-generation
`--check` commands pass. The dispatcher has eight blocks, including the
inlined scalar eighty-round body; the AVX2 leaf has nineteen blocks.
The `.original.ll` sidecars retain the exact original function definitions
whose hashes were recorded during extraction; they are definition excerpts,
not standalone LLVM modules. Checking rejects missing kernels, artifact files,
source files or globals, recomputes the operation inventory and global hashes,
and verifies the original definitions, caller symbol, features and flags.
The importer also verifies the enclosing function's exact symbol and signature
before quoting its region. `MLIR/test_sha512_compress.py` exercises negative
checks for incomplete inventories and misidentified regions. These checks
make the recorded extraction reproducible and inspectable; they do not prove
the correctness of Rust, LLVM or MLIR translation.

`MLIR/import_sha512_compress.py` quotes each exact compiler region using RIR's
ordinary instruction translation. Only necessary symbol quoting is changed.
External calls and global addresses remain explicit. The generated Lean
quotes preserve all operations. RIR now supports the two previously missing
operations: same-allocation pointer equality/inequality in the dispatcher's
input loop and scalar unsigned saturating subtraction in the AVX2 loop.
Both propagate poison. RIR has no physical address assignment for distinct
allocation identities, so cross-allocation pointer comparisons produce poison;
the dispatcher's cursor and end pointer derive from the same input allocation.
The RIR tests cover translation, execution, poison propagation, boundary values,
and rejection of unsupported operand shapes and ordered pointer comparisons.

The exact generated `DispatchProgram.lean` and `Avx2Program.lean` compile with
the pinned Lean toolchain. Their finite elaboration/recursion limits accommodate
the large inlined scalar region; use the repository's `--tstack=400000` setting
when invoking Lean directly. On the validation devbox the dispatcher took
41 seconds and 1.64 GiB peak memory; the AVX2 region took 8 seconds and 727 MiB.
The execution proofs below connect these imported RIR functions to
`CompressionSpec`; successful import alone does not establish that connection.
RIR models the loaded values and memory effects, including the loads marked
volatile in the source, but does not model a volatile event trace. Alignment,
alias metadata, target-feature validity, and compiler correctness are also
outside this region-level proof boundary.

The dispatcher proof uses invocation-local cache/global readiness and a framed
observation contract because initializing its cold CPU-feature cache changes
other memory. Both backend choices refine the same compression specification.
The feature-detection instructions have explicit instruction contracts,
separate from the SHA arithmetic proofs.
`Globals.lean` states exact K64/cache readiness and its preservation through
private-frame erasure and separate scratch/output writes. `Effects.lean`
permits only a legal cache transition followed by the public store. An already
initialized Boolean cache remains unchanged, giving a whole-memory equality
with the legacy single-store effect. `ContextContract.lean` and
`FinalizerContracts.lean` state cold-capable contracts and warm exact-store
corollaries. The bulk contract covers arbitrary supported complete-block
counts, including zero, and derives the one-block contract used by padding.
`ContractAudit` validates the same standard-axiom-only closure for these
structural implications.

`ScalarBulkCall.lean` proves the inlined scalar backend for arbitrary live block
counts. `Avx2ExecutionBulkCall.lean` proves the exact AVX2 call for zero, one,
positive even and larger odd counts. The odd prologue consumes one block; the
pair loop then advances by 256 bytes and feeds the first block's compression
result into the second. Its readiness follows from the emitted entry blocks.
The live input allocation supplies the count and pointer-arithmetic bounds;
no digest result or loop-execution assumption is supplied. The returned memory
is exactly the original memory with the specified 512-bit chaining-state
store. All three private allocations are erased by RIR's call cleanup, while
the allocation counter increases by three. `bulk_call_equation` and
`bulk_contract` expose this result to the dispatcher.

The common `CompressContractUnder` ABI conservatively requires
`SmallRange state.mem data (128 * count.toNat)`, including at zero count.
This excludes an unallocated dangling pointer used for an empty Rust slice.
The stronger `bulk_zero_call` theorem in `Avx2ExecutionBulkZero.lean` requires
only initial memory well-formedness and accepts arbitrary chain and data
pointers. At zero count, caller memory is unchanged and the allocation counter
increases by three.
Callers admitting dangling empty slices must use this stronger result or
weaken the common ABI's zero-count liveness requirement.

`InitializerData.lean` records the extracted K64 and cold-cache initializers.
`InitializerLink.lean` proves that the K64 bytes equal the independent FIPS
table and provides a concrete loader with proved readiness and memory
well-formedness. `Avx2ExecutionConstants.lean` derives the constant-pair facts
used by the backend from this source data. Separately,
`FinalizationDispatchInitializer.lean` quotes the SHA-specific CPU-cache
initializer and proves it equal to the checked initializer after resolving its
cache address. `linked_initializer` in `FinalizationDispatchLinked.lean`
discharges its execution from the CPUID, gated XGETBV and monotonic cache-store
instruction contracts; no whole-initializer execution premise remains.

`FinalizationDispatchComplete.lean` combines these results into
`linked_compress_contract`, covering the actual scalar and AVX2 dispatch paths
with cold or warm caches. It also exports `linked_finalizer_contract` and
`linked_challenge_call`, connecting the imported padding, compression and wide
reduction bodies to the specified scalar derived from SHA-512 of
`R || A || message`. These theorems retain invocation-local memory/global
conditions and the external hardware instruction contracts; they require no
compressor, finalizer or whole-challenge correctness premise. The specified
value is independent of which backend the feature test selects.
`Avx2ExecutionBulkCallAudit` prints the endpoint axiom dependencies;
`FinalizationDispatchCompleteAudit` rejects dependencies outside the same
standard three. These are proofs of the imported RIR execution semantics,
within the translation and machine-semantics boundaries stated above.

The normative specification is
[FIPS 180-4](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf),
sections 4.1.3, 4.2.3, 5.3.5 and 6.4.2. A lightweight Python design check,
reading the new Lean constants and IV, agreed with `hashlib.sha512` on message
lengths 0, 3, 111, 112, 127, 128, 255 and 1024. Two hundred deterministic
arbitrary block/state cases also agreed at every round between the independent
algorithm, the scalar ring schedule, and the AVX pair-window schedule. The
original dependency object's 640-byte K64 allocation was compared byte for
byte with the independent constants, and both backends reference that same
allocation. These are supplemental checks, not Lean execution results or
implementation proofs; the kernel-checked initializer and execution links
described above provide the formal connection.

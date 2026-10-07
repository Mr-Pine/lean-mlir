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
arithmetic results do not claim a connection to imported execution, and no
completed backend refinement is claimed here.

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
Importing these definitions is not a proof that either backend refines
`CompressionSpec`: the concrete round/schedule and memory proofs remain open.
RIR models the loaded values and memory effects, including the loads marked
volatile in the source, but does not model a volatile event trace. Alignment,
alias metadata, target-feature validity, and compiler correctness are also
outside this region-level proof boundary.

The dispatcher cannot satisfy the legacy all-state, chain-store-only contract
as written: initializing its cold CPU-feature cache changes other memory.
Its proof must use invocation-local cache/global readiness and a framed
observation contract. Both backend choices must refine the same compression
specification; digest equality then does not depend on CPUID accuracy. The
feature-detection instructions themselves are not part of an SHA round proof.
`Globals.lean` states exact K64/cache readiness and its preservation through
private-frame erasure and separate scratch/output writes. `Effects.lean`
permits only a legal cache transition followed by the public store. An already
initialized Boolean cache remains unchanged, giving a whole-memory equality
with the legacy single-store effect. `ContextContract.lean` and
`FinalizerContracts.lean` state cold-capable obligations and warm exact-store
corollaries. The bulk contract covers arbitrary supported complete-block
counts, including zero, and derives the one-block contract used by padding.
All four contextual modules compile; `ContractAudit` validates the same
standard-axiom-only closure for their structural implications. No correctness
of the CPUID result is assumed: either backend must produce the same specified
digest. These interfaces are not substituted for the outstanding concrete
execution proofs.

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
implementation proofs; a kernel-checked initializer link is still needed.

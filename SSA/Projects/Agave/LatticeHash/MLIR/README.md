# Compiler extraction artifacts

`generated/kernels.ll` and `generated/kernels.mlir` were compiled from pinned
Agave `arch.rs` using Rust 1.98.1 / LLVM 22.1.8 and MLIR 22.1.8. `extract.py`
verifies the source hash, preserves the entire source verbatim, appends exported
observation wrappers, invokes rustc and MLIR, and records commands, versions and
hashes in `generated/manifest.json`.

The harness supplies the parent `Batch`, `LaneBuf`, `BLOCK_LEN`, `MAX_LANES`
and `LtHash` declarations. This extracts actual kernel bodies in a small
harness; it is not a full production Agave crate build. The wrapper ABIs are
compiler-generated Rust ABIs, including indirect vector arguments and return
storage. Both full-width batch functions, both `compress_pre` helpers, G, transpose,
and packed addition are present.

`extract_portable.py` independently compiles exact function bodies and constants
from locked BLAKE3 1.8.7 `portable.rs`, `lib.rs`, and `platform.rs`. Source hashes
and byte ranges are in `generated/portable_manifest.json`. It supplies type
aliases, adds inline attributes, and exports wrappers. Its `portable.ll` and
`portable.mlir` were not generated from the Lean scalar model.

`lift.py` extracts printed function regions into Lean quotations and SLLVM
CFGs, plus straight-line `Com` definitions. It strips only module-local
`alias_scopes` and `noalias_scopes` metadata attributes; computational operations
remain unchanged. Complete original MLIR is retained. The
`noalias.scope.decl` instruction is retained. Full batch files initially contain
regions only; `BatchCFG8.lean` and `BatchCFG16.lean` supply the explicit
bounds-panic callee contract when lifting them to CFGs.
`generated/regions.json` records operation inventories and extracted hashes.

## Checked execution layer

`SSA.Projects.Agave.LatticeHash.MLIR` imports the completed execution proofs
and their guarded axiom audit. `BatchCFG.lean` is retained as a compatibility
re-export of the two width-specific CFG modules. `BatchOutputRead16.lean` is a
retained output-chunk helper superseded in the main proof chain by
`BatchReadback16.chunks_read_halfword`. Both remain imported and checked.
Its current exported contracts include:

| Component | Execution theorem |
|---|---|
| Portable BLAKE3 G | `agave_portable_g_conforms` |
| Eight-lane G | `agave_g_8_conforms` |
| Sixteen-lane G | `agave_g_16_conforms` |
| Packed wrapping addition, eight lanes | `agave_add_u16_8_conforms` |
| Packed wrapping addition, sixteen lanes | `agave_add_u16_16_conforms` |
| In-place transpose, eight and sixteen lanes | `transpose8_denote`, `transpose16_denote` |
| Emitted schedule global, all 112 entries | `scheduleGlobalWords_lookup`, `scheduleGlobal_load` |
| Complete SIMD `compress_pre` helpers (pre-feed-forward state), including all seven rounds and stores | `agave_compress_pre_8_run`, `agave_compress_pre_16_run` |
| SIMD `compress_pre` scalar refinement and pre-feed-forward word readback | `agave_compress_pre_8_readback`, `agave_compress_pre_16_readback` |
| Complete portable `compress_pre` helper and reference readback | `portable_reference_run`, `portable_reference_readback` |
| Actual portable `compress_in_place` execution and CV memory readback | `portable_in_place_run`, `portable_in_place_readback` |
| Matching-input portable/AVX2/AVX512 pre-feed-forward word equality | `compression_three_way_readback` |
| Actual portable `compress_xof` execution, including feed-forward and output stores | `portable_xof_run`, `portable_xof_reference_conforms` |
| Actual portable XOF byte readback for each supplied root-output counter | `portable_xof_call_readback`, `portable_xof_root_output_readback` |
| Actual portable helper sequence for every message of at most 1024 bytes, with all 2048 output bytes | `PortableShort.short_run` |
| Closed portable execution existence and all 1024 LtHash limb observations | `PortableShort.short_run_exists` |
| Byte-addressed result observation | `outputMem_read_lane`, `portableCompressionMemory_read_word` |
| Batch scratch allocation, both widths | `BatchEntry.entry8_denote`, `BatchEntry16.entry16_denote` |
| Eight-lane batch header and guarded input loads | `BatchHeader.run8`, `BatchLoads.block*_continue` |
| Eight-lane batch transpose and root retention | `BatchFirstTranspose.first8_run`, `BatchTranspose.transpose8_run`, `BatchRootCopy.block18_continue` |
| XOF counter initialization | `BatchXof.block22_continue` |
| Concrete retained-store caller allocation | `CallerMemory.materialization_exists` |
| Retained bytes and length metadata loaded from memory | `CallerMemory.Represents.read_source_words`, `CallerMemory.Represents.read_length_run` |
| AVX2 loop load premises derived from caller/frame invariants | `CallerMemory.represented_loads8` |
| Both loaded/transposed batches identify scalar message blocks | `CallerMemory.columns8_scalarBlock`, `CallerMemory.columns16_scalarBlock` |
| Complete AVX2 batch execution and all 1024 stored accumulator cells | `BatchConformance8.run_readback`, `BatchConformance8.run_portableLtHash` |
| AVX2 full-width invocation existence and refinement | `BatchConformance8.fullWidth_total`, `BatchConformance8.fullWidth_refines` |
| AVX2 accepted lifecycle output logs | `Execution.Avx2.run_refines_log`, `Execution.Avx2.noSerial_run_refines_log` |
| AVX2 execution existence for every accepted trace, given reference-correct serial executions | `Execution.Avx2.every_legal_trace` |
| Unconditional AVX2 compiled-flush and drain witness with serial calls disabled | `Execution.Avx2.eight_empty_compiled_witness` |
| Complete AVX512 batch execution and all 1024 stored accumulator cells | `BatchConformance16.run_readback`, `BatchConformance16.run_portableLtHash` |
| AVX512 full-width invocation existence and refinement | `BatchConformance16.fullWidth_total`, `BatchConformance16.fullWidth_refines` |
| AVX512 normal termination and finite successful CFG evaluation | `BatchExecution16.terminates`, `BatchExecution16.terminates_eval` |
| AVX512 accepted lifecycle output logs | `Execution.Avx512.run_refines_log`, `Execution.Avx512.noSerial_run_refines_log` |
| AVX512 execution existence for every accepted trace, given reference-correct serial executions | `Execution.Avx512.every_legal_trace` |
| Unconditional AVX512 compiled-flush and drain witness with serial calls disabled | `Execution.Avx512.sixteen_empty_compiled_witness` |

The kernel theorems execute the lifted programs on arbitrary input words in
byte-backed memory. Their premises describe allocated input/output storage,
input contents, and caller state. Their conclusions give the stored result
and preserve unrelated allocations. `g_threeway_lane` connects the three
G implementations to the same scalar arithmetic specification. No premise
assumes that an implementation already computes the correct result.

The transpose theorems equate the complete read/write program with an
independent mathematical matrix transpose, including its SLLVM memory effects.
The complete portable and SIMD `compress_pre` helper theorems execute entry
loads, all seven compiled rounds, and every output store. Every lane may have
unrelated input words and counters. The readback theorems identify each actual stored u32 with
the scalar pre-feed-forward state. These helpers do not perform BLAKE3
feed-forward or produce the final LtHash output. Their premises concern
initialized caller memory and the emitted schedule, rather than the correctness
of a round or return value.
Output readback also requires a no-wrap bound on pointer offsets, so the
observations address the intended contiguous bytes.

`compression_three_way_readback` proves that the independently compiled
portable, AVX2, and AVX512 helpers return matching pre-feed-forward words for
matching logical inputs. Other vector lanes remain unrestricted.
`portable_in_place_readback` executes the compiled in-place helper and observes
all eight stored chaining-value words as `scalarCompressCV`, preserving every
other allocation. Its memory lemmas retain storage bounds and derive each
physical CV word read.
`PortableXofReference.lean` additionally executes the actual compiler-produced
portable `compress_xof` CFG, including all sixteen feed-forward XORs and the
output stores. `portable_xof_call_readback` observes its 64 serialized bytes
through real 8-bit memory reads. `portable_xof_root_output_readback` identifies
those bytes with the independent reference's root output for any counter from
0 through 31. These per-call results accept a supplied root descriptor.
`PortableShortRun.lean` removes that premise by composing actual helper bodies
for every message of at most 1024 bytes. `PortableShort.short_run_exists`
constructs IV, padded-message, and zero-output allocations from `emptyState`,
executes the required nonroot `compress_in_place` bodies followed by all 32
`compress_xof` bodies in one continuous memory image, and proves every one of
the 2048 output bytes and 1024 little-endian u16 limb observations equals the
independent portable LtHash reference. Message length is its only premise.

This portable composition supplies padded staging, helper-call scheduling,
and root flags in Lean. It invokes each extracted helper's raw `.denote`;
it does not extract Rust `Hasher` control flow or establish the call-frame ABI
of that helper sequence. The public serial fallback and arbitrary long-message
streaming remain separate. The earlier pure observer in
`PortableObservation.lean` remains an auxiliary result.

`GeneratedGlobals.lean` is generated from the compiler-emitted schedule bytes,
independently of the mathematical schedule. `GlobalsProof.lean` proves every
entry agrees and derives all schedule memory reads from its initialized-global
contract. `scheduleGlobal_withGlobal` establishes that contract by installing
the emitted bytes with SLLVM's global loader.

`AxiomAudit.lean` rejects changes to the exported theorems' logical axiom
dependencies. The checked contracts use only `propext`, `Classical.choice`,
and `Quot.sound`; there is no native proof evaluation or custom axiom.

The complete AVX2 and AVX512 batch theorems start from concrete retained caller
images and execute their compiler CFGs through guarded message loads, masked
lane updates, all compression rounds, root retention, all 32 XOF counters, and
accumulator stores. They observe every one of the 1024 u16 cells in the resulting
memory. `BatchConformance8.run_portableLtHash` and
`BatchConformance16.run_portableLtHash` identify each 2048-byte result with the
fold of independent portable LtHash reference values into the initial
accumulator. Caller staging invariants discharge message lengths, padding,
load bounds, and schedule requirements. Each `fullWidth_total` constructs an
actual invocation from the empty caller base; execution existence is not
assumed. The termination proofs also yield finite successful CFG evaluations.

`CallerMemory.lean` constructs disjoint byte-backed source, length, accumulator,
and global allocations from an arbitrary retained `AgavePhysicalStaging.Store`.
The construction uses no compression or hash result. It preserves stale suffix
bytes exactly. `CallerPacking.lean` groups these bytes into little-endian words
and derives metadata bounds and padding validity from the existing physical
staging invariant. `CallerBatch8.lean` and `CallerBatch16.lean` connect actual
row reads and transpose outputs to scalar blocks, including stalled root lanes.

`Execution.lean` defines `FullWidthRun`, `Flush`, `Commit`, `Take`, and an
event-indexed `Run`. Full-width results come from normal executions of the
actual batch CFG and successful reads of all 1024 output cells. The outer
staging/event transitions remain source-shaped; their Rust bodies have not
been extracted. Each batch leaf embeds the retained store into a concrete
caller memory image.

`Lifecycle8.lean` and `Lifecycle16.lean` prove that AVX2 and AVX512 runs refine
the same complete public output-log specification for accepted ordinary
finish-or-drop traces. `run_refines_log` requires
explicit refinement of serial leaves for partial tails and messages longer
than 1024 bytes. `every_legal_trace` constructs executions given the existence
of reference-correct serial executions. `noSerial_run_refines_log` uses the
empty serial relation, so it requires no external serial correctness premise.
`Execution.Avx2.eight_empty_compiled_witness` in `Reachable8.lean` and
`Execution.Avx512.sixteen_empty_compiled_witness` in `Reachable16.lean`
unconditionally construct traces of eight and sixteen empty whole messages,
respectively, a compiled full-width flush, and a drain with serial calls
disabled. They prove the observed output equals the public specification,
establishing that each serial-free relation contains an actual compiled
invocation. These results do not establish compiled serial execution.

Forgotten/leaked-builder transitions are excluded. This is not unrestricted
safe-Rust API equivalence: the clean-state `take_lt_hash` check is debug-only,
and the source-model `ForgottenOutput.lean` proves release-mode divergence
after a forgotten builder. The lifecycle boundary is described in the
[parent README](../README.md#necessary-lifecycle-boundary).

## Reproduction

On an x86-64 Ubuntu Noble-compatible remote worker:

```sh
python3 install_tools.py /tmp/agave-llvm22
export LD_LIBRARY_PATH=/tmp/agave-llvm22/root/usr/lib/x86_64-linux-gnu
python3 extract.py --agave /path/to/pinned/agave --out generated \
  --rustc /path/to/rust-1.98.1/bin/rustc \
  --mlir-translate /tmp/agave-llvm22/root/usr/lib/llvm-22/bin/mlir-translate
python3 extract_portable.py --blake3 /path/to/blake3-1.8.7 --out generated \
  --rustc /path/to/rust-1.98.1/bin/rustc \
  --mlir-translate /tmp/agave-llvm22/root/usr/lib/llvm-22/bin/mlir-translate
python3 extract_portable_xof.py --blake3 /path/to/blake3-1.8.7 --out generated \
  --rustc /path/to/rust-1.98.1/bin/rustc \
  --mlir-translate /tmp/agave-llvm22/root/usr/lib/llvm-22/bin/mlir-translate
python3 lift.py .
lake build SSA.Projects.Agave.LatticeHash.MLIR
lake build SSA.Projects.SLLVM.Tests
```

With dependencies already built, checking the direct 890-operation portable
compression theorem took 46m32s on the development worker and produced a 47 MB
`.olean`. This is a measured build cost, not a time bound; cached reference
wrappers check in seconds.

The installer extracts checksum-pinned official LLVM packages without a system
install. Host paths and Rust crate hashes can affect compiler metadata;
provenance records the exact paths used for the checked-in artifacts.

The separate `portable_xof_harness.rs` compiles the locked BLAKE3
`compress_xof` and `compress_in_place` bodies, together with their original
supporting function and constant spans. Supplied `inline(always)` attributes
and two exported wrappers are recorded harness instrumentation; calls to
`compress_pre` retain their original binding and are inlined by the compiler.
`portable_xof_manifest.json` records exact byte spans, compiler versions,
commands, and hashes. Its LLVM/MLIR module is appended during lifting, so the
original twelve Lean/MLIR regions and message-schedule artifacts remain
byte-for-byte unchanged. The provenance lock retains those original region
hashes explicitly.

## Remaining boundary

Extraction removes manual transcription of each quoted kernel body. It does
not verify Rust compilation, MLIR import, harness ABI agreement with production,
or machine code. SLLVM's memory model and treatment of LLVM flags remain
relevant: ignored load/store alignment, GEP `noWrapFlags` / `inbounds`, Rust alias guarantees, and
function argument attributes are not a proof of full LLVM definedness. These are execution theorems for SLLVM; their memory premises can describe
states outside the source language’s valid aligned/reference domains. The
SIMD full-batch and lifecycle results above retain these boundaries; runtime
dispatch and compiled scalar fallback are not verified.

The batch CFG's nonreturning bounds-panic callee has an explicit undefined
behavior contract. A successful batch refinement must exclude that path
from its input invariant. Vector `freeze` uses SLLVM's deterministic
poison-to-zero choice; a proof covering every LLVM choice must establish
that these operands are defined.

## Read-only verification

Run `python3 verify.py` without Rust, LLVM, MLIR or Lean installed. Optionally
supply `--agave /path/to/agave --blake3 /path/to/blake3-1.8.7` to verify the
external source files and each portable source byte span. The verifier checks
source pins, recorded compiler versions, original artifact hashes, the exact
set of 14 exported regions, and regeneration of all generated Lean files in a
temporary directory. It independently checks that region extraction removed
only alias metadata. For the XOF module it independently recovers each bounded
source declaration, checks the complete harness scaffold and original call
bindings, and validates compiler command flags. It never rewrites artifacts or manifests.

`provenance.lock.json` pins extraction manifests and all pipeline scripts,
including the verifier. Its trust anchor is the reviewed source-control
snapshot, not a signature or a proof of compiler correctness. A coordinated
change to the lock and its inputs requires review. New compiler artifacts
require an explicit reviewed update of their manifests and this lock.

`python3 test_verify.py` exercises the pristine case and mutations of original
Rust, LLVM, MLIR, a source wrapper, generated Lean/regions, compiler version
metadata, and the lift script. Additional cases update artifact/manifest hashes
after changing an XOF source body, wrapper, compiler command, or span; the
independent structural checks must still reject them. Every mutation must be rejected.

`GeneratedGlobals.lean` is generated from the actual 896-byte message-schedule
initializer in the compiler's MLIR, decoded as 112 little-endian `u64` words.
It does not read the Lean schedule model. `verify.py` independently decodes the
original initializer and checks both its byte hash and the generated literal;
mutation tests cover the literal and its companion JSON inventory.

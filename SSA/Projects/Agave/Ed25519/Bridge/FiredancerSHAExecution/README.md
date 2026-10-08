# Pinned Firedancer SHA execution proofs

This directory imports all four scalar Firedancer SHA-512 bodies into RIR
and SLLVM and proves their complete reachable calls. The RIR transcript
endpoint is `TranscriptInvocation.fresh_correct`; the SLLVM core, append,
and finalizer proofs supply the actual SHA calls in the existing reference
verifier through `verifierTailCalls`. Both compute the standard original-byte
`R || publicKey || message` digest without a compression/execution/digest premise.
See [SLLVMSourceBoundary.md](SLLVMSourceBoundary.md) and the
[parent proof ledger](../ProofClosureLedger.md) for final endpoints and validation.

## Source and reproduction

The pin is Firedancer commit `292f89b338a634e23e9f45c3dfdd5383ddcae624`.
`manifest.json` records all C/header dependencies, SHA-256 hashes, exact
compiler/tool versions and commands, generated artifact hashes, and per-region
operation counts. The source C file's most recent change at that pin is commit
`8b07f367bdd9a3df9ec9a0526aafe41448dee471` (RISC-V SHA acceleration).
The extraction explicitly selects `FD_SHA512_CORE_IMPL=0`, disables AVX/AVX512,
and uses Clang 21 `-O1` with vectorization and loop unrolling disabled. It does
not claim to represent a build that selects an accelerated backend.

Run `python3 import.py --source /path/to/firedancer` to reproduce with the
recorded LLVM 22 tools, or supply `--clang`, `--llvm-bin`, and `--llvm-lib`.
`python3 import.py --check` checks stored hashes and deterministically
regenerates both Lean imports without requiring the C checkout. Extraction
uses Clang's normal inlining, then `llvm-extract` and global dead-code removal;
there is no instruction rewrite, synthetic C wrapper, or post-Clang inlining.
LLVM/MLIR compilation and the source-to-artifact correspondence are trusted
steps; Lean checks the imported RIR definitions and proof terms.

## Checked pieces and linkage

- `Program.lean`: exact body regions for init (1 block), core (6 blocks), append
  (11 blocks), and finish (3 blocks). All operations are accepted by the existing
  RIR importer. The only external call symbol in append/finish is the core;
  memcpy/memset, rotations, byte swaps, and lifetime operations use RIR semantics.
- `Initialize.lean`: exact full init execution and call, with eight 64-bit IV
  stores at context offsets 128 through 184 and a 24-byte zero store at 200.
  Assumptions are caller state well-formedness and a live small allocation
  containing the first 224 bytes. The complete resulting memory is specified,
  so the buffer (0–127), magic (192–199), and padding are outside the writes.
  Allocation state and every other memory block are unchanged.
- `AppendZero.lean`: exact two-block return path for size zero, for arbitrary
  supplied core semantics and arbitrary (even poison) pointer values. No memory
  read/write or core call occurs. Full call equality needs only state WF.
- `InitializerData.lean` and `InitializerLink.lean`: the 80 words extracted from
  `fd_sha512_core_ref.K` equal the independently specified standard constants;
  explicit RIR global installation supplies those bytes and preserves WF.
- `Linked.lean`: append and finish call the **actual imported core CFG**, through
  `Func.call`; the linked empty append theorem needs no compression assumption.
- `Audit.lean`: kernel axiom closure of the checked execution/data endpoints.
- `Arithmetic.lean`, `CoreRounds.lean`, `RingSchedule.lean`: exact source
  Boolean/rotation/addition expressions refine the common SHA round and schedule;
  the circular 16-word schedule preserves its relation to all 80 standard words.
- `CoreSchedule.lean`, `CoreFirst.lean`, `CoreLater.lean`: complete imported
  first-round and later-round instruction bodies, including safe stack/table
  indices, ring writes, and exit tests. `CoreInputMemory.lean` relates native
  input loads and byte swaps to the common big-endian block words, and proves
  incremental initialization of the ring memory.
- `Context.lean`: the concrete 224-byte context relation to completed blocks,
  pending bytes, chaining words, and a wrapping 128-bit bit count; actual init
  establishes it. `AppendCounter.lean` proves the nonempty counter-update block,
  including carry and memory preservation outside the context allocation.
- `FinishPadding.lean`: actual marker/branch body and the zero-fill/length-store
  prefixes before the core calls. `FinishOutput.lean` proves the complete
  post-core output instruction suffix as eight byte-swapped word stores.
- `SourceAudit.lean`: strict transitive axiom audit of 110 source-leaf endpoints,
  allowing only `propext`, `Classical.choice`, and `Quot.sound`.
  `source-leaves-manifest.json` freezes their source and compiled hashes, exact
  repository dependency source hashes checked against the validation checkout,
  toolchain/package lock hashes, and scope. `source-leaves.paths0` is the exact
  NUL-delimited file list for this slice. These are instruction-body and
  arithmetic results; they do not assert complete core or streaming execution.

The recorded target is x86-64 Linux LP64, little-endian. The context layout is
buffer at 0, eight words at 128, magic at 192, used-byte count at 200, and low/high
bit counts at 208/216; the C object has 128-byte alignment and 256-byte footprint.
RIR models pointers by allocation and offset. Native alignment, calling
conventions, target representation, and function/argument attributes remain
part of the source/LLVM boundary; region import is not a native ABI theorem.
The LLVM core function uses `fastcc`; its two callers and definition agree in
the artifacts. Linking here uses RIR's exactly typed parameter order
`[ptr, ptr, bv64]` and its private-frame cleanup semantics.

## Complete call proofs

`CoreMultiBlocks` and its supporting loop/frame modules close RIR compression
for every positive block count satisfying readiness. The zero-count entry is
excluded because the extracted core uses a do-while loop. `AppendLinked`
and the `AppendSemantic*` proofs establish append execution and the streaming
invariant. `FinishCompositionSource` establishes actual padding/finalization and the
standard digest. `TranscriptCorrect*` composes init and all three appends
with finalization and supplies a fresh-context theorem.

The `SLLVMSourceCore*`, `SLLVMAppend*`, and `SLLVMFinish*` modules independently
prove the corresponding SLLVM calls; the two interpreters' states are not
identified. The allocation-independence adapter supplies the exact block
contract required by the reachable verifier proof. The existing broad
contracts over malformed/unreachable states remain available as generic
interfaces, but are not assumptions of the final comparison.

Source extraction, native/compiler refinement, and identity of the older
unpinned verifier lift with a newer source revision remain separate boundaries.
The complete source-linked comparison and explicit-memory corollary are in
`Bridge/CrossClientReachableConcrete.lean` and `Bridge/CrossClientLoaded.lean`.

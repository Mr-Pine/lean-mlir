# Pinned Firedancer SHA execution work

This directory imports all four scalar Firedancer SHA-512 bodies into RIR. It
proves the complete initializer call, the zero-length append call, and the
actual extracted constant table's equality to the existing SHA-512 specification.
It does **not** provide `FiredancerShaInitBy`, `FiredancerShaAppendBy`,
`FiredancerShaFinishBy`, or `DigestBy` witnesses.

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

The recorded target is x86-64 Linux LP64, little-endian. The context layout is
buffer at 0, eight words at 128, magic at 192, used-byte count at 200, and low/high
bit counts at 208/216; the C object has 128-byte alignment and 256-byte footprint.
RIR models pointers by allocation and offset. Native alignment, calling
conventions, target representation, and function/argument attributes remain
part of the source/LLVM boundary; region import is not a native ABI theorem.
The LLVM core function uses `fastcc`; its two callers and definition agree in
the artifacts. Linking here uses RIR's exactly typed parameter order
`[ptr, ptr, bv64]` and its private-frame cleanup semantics.

## Remaining dependency graph

1. Prove the imported core's stack/schedule memory safety and its first-16 and
   circular-schedule remaining-64 round loops refine
   `Agave.Ed25519.SHA512.Spec.compressBlock`, then iterate over positive block
   counts. The C core is a do-while loop; zero block count is not a valid
   compression entry case. Reusing the Agave **specification and arithmetic**
   is appropriate; an Agave machine-body theorem is not a theorem about this
   different Firedancer CFG.
2. Use that core refinement to prove nonempty append's counter arithmetic,
   partial-buffer/full-block split, and exact state/memory frame; establish the
   invariant `buf_used < 128` and the 128-bit message-length interpretation.
3. Prove finish's one/two padding blocks, big-endian bit length, eight output
   byte-swapped words, and alias/range conditions. Compose into a streaming
   SHA-512 result for `R || A || message`.
4. Connect to the existing bridge contracts. `FiredancerShaPrograms` and
   `FiredancerSha*By` currently quantify **SLLVM.Cfg**, SLLVM `GlobalState`, and
   `LiveBlock` transformers. These new bodies are **RIR.Func** and RIR states.
   A proved state/program simulation or independently imported/proved matching
   SLLVM bodies is required; type-compatible witnesses cannot be obtained by
   simply plugging these RIR definitions into those contracts.
5. Establish correspondence of the pinned source/version to the legacy
   verifier lift if reusing that exact SLLVM program. The legacy source file
   names a local build path but contains no source-commit pin; no equality
   between that lift and this newer pinned revision is asserted here.
6. The established stream refinement can then inhabit `DigestBy` via the
   existing `digestBy_of_stream` theorem. None of steps 1–5 is replaced by a
   new axiom, assumed compression contract, or a legacy determinism axiom here.

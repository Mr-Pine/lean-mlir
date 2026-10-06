# SHA-512 boundary and padding refinement

`Padding.lean` fixes SHA-512 padding and digest byte order by definition and
proves semantic finalization from complete-block compression. `digest_eq_of_block_agrees` reduces cross-backend
semantic digest equality to equality on a **single 128-byte compression block**,
using the proved block-fold and padding composition lemmas. In particular,
`finalize_transcript` identifies the digest of the original `R || A || message`
bytes; it has no independent whole-hash correctness premise. `Compression.run`
still abstracts complete-block SHA-512 compression and supplies its empty and
block-aligned composition laws. A concrete 80-round SHA-512 specification and
its implementation refinement have not been supplied by this module.

The existing challenge ABI can use `SHA512.model compression`; its `digest`
is defined from that same compression operation, the extracted initial state,
SHA-512 padding, and per-u64 big-endian output serialization. This rules out an
unrelated arbitrary digest function in that instantiation. It does not prove
`ScalarFromSha512Contract` for the imported machine program.

## Exact Agave call boundary

The original pinned `challenge_scalar` hashes 32 original R bytes, 32 original
A bytes, and the message. Its external symbols are `sha2::sha512::compress512`
and `ed_sigs::scalar_from_sha512`. The latter receives the 208-byte context:
127 buffer bytes, one byte of buffer length, eight native u64 chaining words,
and a u128 completed-block count.

`MLIR/extract_sha512.py` extracts that **original** `scalar_from_sha512` from
the complete crate IR already pinned by the main manifest. It does not rewrite
Rust, synthesize LLVM instructions, or change optimization/inlining. The new
artifact has four CFG blocks, 70 allocations, 65 singlethread seq_cst fences,
140 stores, and only two external primitive symbols: compression and
`Scalar::from_bytes_mod_order_wide`. The latter has a separate scalar-reduction
proof in this development. The padding branch is `(pending_len XOR 112) < 16`,
and the length field is `bswap128((block_count << 10) OR (pending_len << 3))`.
`needsTwoBlocks_iff` checks that exact XOR cutoff; `bitLength_arithmetic`
identifies the shifted OR with eight times the total transcript byte count.

`ExecutionProgram.lean` is generated from the exact full region, including all
zeroization stores and fences. The RIR fence constructor explicitly records
`syncscope="singlethread", ordering=7`, with state-preserving effects in the
sequential memory model. Other fence orders/scopes remain rejected. This is
not a proof of LLVM concurrent or signal-handler behavior or volatile traces.

## Firedancer inventory

`Firedancer/Common/Spec/SHA.lean` still declares `fd_sha512_init`,
`fd_sha512_core_ref`, `fd_sha512_append`, and `fd_sha512_fini` as opaque Cfg
axioms. Its four additional assumptions specify determinism and memory
footprint, not SHA-512 digest correctness. There are no existing lifted
Firedancer SHA wrapper/compression programs or correctness proofs in this
checkout to reuse. Consequently this module does not close Firedancer's hash
execution gap, and no cross-client unconditional digest equality is claimed.

## Remaining execution obligations

The semantic padding proof does not replace the actual wrapper proof. The
imported Agave wrapper still needs its four-block memory execution proof:
70 allocations/lifetimes, zero fills and copies, actual counter arithmetic,
nine byte swaps, compression calls, scalar-reduction call, and zeroization.
Compression must then be connected to a concrete shared SHA-512 round spec.
Firedancer's init/append/fini implementations need extraction and analogous
memory refinements. Only after these steps can the remaining hash contracts in
the end-to-end verifier be removed. The standard-three axiom audit cannot
substitute for any of these explicit obligations.

## Checks

Run the two artifact checks from the repository root:

```
python3 SSA/Projects/Agave/Ed25519/MLIR/extract_sha512.py --check
python3 SSA/Projects/Agave/Ed25519/MLIR/import_sha512.py --check
lake build SSA.Projects.Agave.Ed25519.Proof.SHA512.Audit
```

The first two check provenance and exact regeneration. The Lean audit checks
padding/control theorems, successful exact-region import, and focused fence
semantics/parser tests; it allows only `propext`, `Classical.choice`, and
`Quot.sound` in their transitive axiom closures.

On 2026-10-07 both Python checks passed and the pinned local toolchain completed
`SHA512.Audit` successfully (2040 build jobs; `/tmp/sha512-audit-build.log`).
The eleven selected endpoints passed their guarded standard-three closure
check. A devbox validation attempt was blocked by Teleport authentication
expiry (`timed out waiting for callback`), so this records local kernel
validation only and does not claim a fresh devbox audit.

# Checked bytewise adapter and linkage evidence

`BcmpByteABI.lean` reduces the remaining comparison premise to the ordinary
meaning of one `bcmp(left, right, 32)` invocation: it returns a defined i32,
and that result is zero exactly when all 32 corresponding bytes are equal.
The module **does not discharge this external execution premise**. No
implementation of `bcmp` is present in the pinned LLVM input.

The [legacy Open Group specification](https://pubs.opengroup.org/onlinepubs/007904875/functions/bcmp.html)
states this bytewise zero/nonzero behavior. It does not require a normalized
nonzero value or a sign. This is the portable semantic fact used by the
adapter, independently of whether a particular libc offers stronger `memcmp`
behavior. The historical specification is documentation for the premise, not
an axiom or a proof that a deployed implementation meets it.

## What Lean checks

All names below are in
`Agave.Ed25519.Verifier.Execution.Dalek.Bcmp.ByteABI`.

* `Input32` requires a live 256-bit read and representability of the last byte
  address, at offset 31. It does not require a representable one-past address,
  alignment, disjointness, or allocation length below `2^63`.
  `input32_of_smallRange` derives it from the existing verifier invariant.
* `equal32_iff_readAt` proves equality of the 32 individual byte loads is
  equivalent to equality of the bulk 256-bit RIR reads. It proves the address
  and bit-index conversions; they are not extra ABI hypotheses.
* `invocation_iff` proves the ordinary bytewise invocation predicate equivalent
  to the existing invocation-local `Bcmp.Invocation`. Successful return and
  zero/nonzero correctness are the only remaining semantic premises for
  acceptance. Both equal and unequal inputs are covered, including embedded
  zero bytes and arbitrary nonzero i32 results.
* `compression_tail` proves the behavior of the actual imported block 10 and
  cleanup blocks 12 and 13. It returns code 255 on byte equality and code 2
  otherwise, exposing the actual resulting state.
* `CallerFrame` preserves the contents and size of each pre-existing memory
  block. It allows arbitrary fresh blocks and allocation-counter changes.
  Its `readAt`, `smallRange`, and `readBytes` theorems recover the caller's
  observations and liveness. `compression_tail_framed` carries this guarantee
  through the same actual cleanup. Neither acceptance nor this frame theorem
  requires final-state `WF`.
* `compareContract_of_bytewise` is the compatibility entry point for the
  existing whole-verifier composition. It proves `CompareContract` from the
  bytewise premise and the existing `ReadOnlyFrame`, which remains explicit.
  The weaker `CallerFrame` alone cannot establish that old contract's
  all-address reads and final-state well-formedness; no such implication is
  claimed or used.

There is no replacement equality routine, imported surrogate, proof of a
separately written comparator, or new axiom. The adapter operates on the
actual `Primitives.compareBytes` passed to the imported verifier.

## Pinned artifacts and deployment inspection

The inspection on 2026-10-07 rehashed the full extraction input:

```text
/tmp/ed25519-rir-extract/final/build/target/release/deps/
  solana_ed25519-7a5ccd2d9f9b85be.ll
SHA-256: 2ea5bd097be748ddb48c0361700c0dacb5ee7146c87f29543001e78261c82dcc
```

It contains one `bcmp` declaration, at line 65578, and no definition. The
selected verifier LLVM artifact has SHA-256
`d98b852297712296b6356fad2a29ff4aff1b815f07d5e05660078b85bb570955`.
Its target is `x86_64-unknown-linux-gnu`; its i64 length is exactly 32, i32
result is observed only by equality to zero, and declaration has
`captures(none)`, `nocallback`, `nofree`, `nounwind`, `willreturn`, and
`memory(argmem: read)`. These compiler annotations do not establish the
bytewise return-value relation. The Rust source at
`MLIR/source/src/ed_sigs/verification_key.rs:423` uses array equality and
does not choose a libc implementation.

The Agave checkout is at the manifest's commit
`e818d643945cd82c7144013af58ccf82d31df2dd`. Its `.cargo/config.toml` selects
`x86-64-v2` for GNU/Linux, while the dedicated extraction uses `x86-64`.
`ci/docker/env.sh` names the mutable base image `ubuntu:22.04`; the Dockerfile
installs system packages with `apt-get`. These files do not pin the final
libc binary, loader resolution, or runtime dispatch. The checked extraction
manifest contains no final linked validator executable or resolved external
symbol. A GNU target alone cannot select a particular implementation body.

### Additional native-object observation

The extraction directory also retains an rlib which was **not hashed by the
original LLVM artifact manifest**:

```text
libsolana_ed25519-7a5ccd2d9f9b85be.rlib
SHA-256: eb73b3f175b1c0e616e0ba0046b7417f08e4d6baa1cbd195da63240aa461d6b3
object member:
  solana_ed25519-7a5ccd2d9f9b85be.solana_ed25519.e5f703a99ceb696b-cgu.0.rcgu.o
object SHA-256: e517972f4e733f6220811de8668a5b40580678728ae01f40af8ed2a46f8e3972
```

GNU binutils 2.46 `nm --undefined-only` reports no undefined `bcmp` or
`memcmp` in this rlib. `objdump -d -C` shows the `verify_dalek` comparison
lowered at function offsets `0x2ba` through `0x2ef` to four `movdqu` loads,
two `pcmpeqb`, `pand`, `pmovmskb`, `cmp 0xffff`, and `sete`/`neg`/`or`.
Thus this observed native object implements the comparison inline; it is
not evidence of a selected libc `bcmp` body. This observation also prevents
overstating the LLVM external symbol as necessarily a deployed dynamic call.

The native object is not a deployed validator, its derivation is outside the
original pinned manifest, and the project has no checked x86-to-RIR lift for
this instruction sequence. No native implementation equivalence is claimed.
Discharging the LLVM-level external boundary would require additional
verified lowering/linkage evidence or a pinned external implementation.
Choosing the current host libc would not supply that missing connection.

## Validation

The new module and `BcmpByteABIAudit.lean` both kernel-check on the shared
devbox with the project toolchain, Lean `nightly-2026-09-16`. The audit checks
all eleven new theorem endpoints and rejects dependencies other than
`propext`, `Classical.choice`, and `Quot.sound`.

The new provenance checker validates the existing manifest hashes, the
external declaration and its attributes, the fixed-length call, the sole
zero-test use, the select, and the imported RIR call signature:

```bash
python3 SSA/Projects/Agave/Ed25519/MLIR/check_bcmp_boundary.py \
  --crate-ir /tmp/ed25519-rir-extract/final/build/target/release/deps/solana_ed25519-7a5ccd2d9f9b85be.ll
```

Omitting `--crate-ir` checks the committed selected artifacts only. The
checker is a reproducible provenance check and does not prove the ABI.

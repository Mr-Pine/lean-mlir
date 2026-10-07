# Exact subgroup scalar wide-reduction boundary

The pinned `Scalar::from_bytes_mod_order_wide` is distinct from the base-field
`Reduce64` kernel. Its input is 64 bytes and its output is 32 bytes modulo
`L = 2^252 + 27742317777372353535851937790883648493`.

`ExecutionProgram.lean` imports the original wide reducer and its
`Scalar52::montgomery_mul` callee. Both are single-block regions. The outer
region contains two Montgomery calls, one byte black-box call, 24 allocations,
11 fences, and two byte globals. The Montgomery region contains one black-box
call, nine allocations, and nine fences. No body rewrite, extra inlining, or
instruction normalization is applied. The RIR model remains sequential and
does not prove volatile-event traces.

`ExecutionGlobals.lean` records the exact 40-byte initializers of R and RR.
`Arithmetic.lean` interprets their five u64 slots as radix-2^52 limbs and checks
that they equal `2^260 mod L` and `2^520 mod L`. It reuses the existing
`Bridge.Challenge` subgroup-order lemmas to combine split-input congruences
and canonicality into exact output equality.

`Contract.lean` states successful execution, the exact 32-byte output, and an
output frame preserving live caller ranges and bytes outside the output. Its
observation theorem explicitly derives unchanged input bytes, little-endian
integer equality modulo L, and the canonical bound from that contract.

`Linked.lean` binds both external routines to the independently extracted
Montgomery and black-box bodies. It also supplies the exact `reduceWide`
function field for `SHA512Finalization.Primitives`. Global addresses and their
initializers remain explicit. **There is no proof of `ExecutionObligation`:**
the complete wide-wrapper memory execution and the Montgomery carry/bounds
refinement remain outstanding. An import, contract definition, linking
function, or pure modular lemma must not be presented as this proof.

`Startup.lean` executes the actual initial 89 wide-body instructions and 33
Montgomery-body instructions, including exact constant/global address writes
and all 24/9 stack allocations. `CallPhases.lean` proves the real call/suffix
boundaries at wide-body indices 320, 324, 376 and Montgomery index 226.
`MontgomeryProduct.lean` executes Montgomery instructions 33–49: lifetime and
scope declarations, two input loads, u64-to-u128 extension, and the first
`mul nuw`. Its product is proved equal to the full natural-number product for
arbitrary u64 inputs. These are partial concrete execution proofs; they do not
cover subsequent carry reduction or the complete wrapper.

## Provenance

The complete pinned crate LLVM SHA-256 is
`2ea5bd097be748ddb48c0361700c0dacb5ee7146c87f29543001e78261c82dcc`.
The extracted wide LLVM SHA-256 is
`3af5a470ac2ec4f002c3abf7ada62e1d02d18bf67bc1e247b8c21f5475ae582b`;
the wide MLIR SHA-256 is
`1f91ae907831e13b7c93d60549d03de6cbb40bf09ec376098cd9f50ebe700750`.
The Montgomery LLVM SHA-256 is
`07f3f1e49ec2ea7470e3da8af1198f8f15eb1cb5ade67f652baa50173024ed79`;
its MLIR SHA-256 is
`2d0f10b723772e48d03534b067b4220829a86c9d1f254c1d63c44ed820678f48`.

`MLIR/generated/scalar-wide-manifest.json` records the exact target symbols,
original-definition hashes, LLVM 22.1.2 tool versions, extraction commands,
and operation inventory. `scalar-wide-rir-manifest.json` records the exact
region hashes, callees, globals, and generated-input hashes.

Import path: `SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Linked`.

## Validation

From the repository root:

```
python3 SSA/Projects/Agave/Ed25519/MLIR/extract_scalar_wide.py --check
python3 SSA/Projects/Agave/Ed25519/MLIR/import_scalar_wide.py --check
lake build SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Audit
```

The two Python checks passed on 2026-10-07. The nine Lean modules were then
compiled sequentially with the pinned local toolchain and `-j1`, emitting
normal-cache oleans. `Audit.lean` passed its guarded standard-three closure
checks for 22 import, arithmetic, contract, linkage, and partial-execution
endpoints. Logs: `/tmp/scalar-wide-*.log`; reproduction wrapper:
`/tmp/check_scalar_wide.sh`. The full audit used 4.76 seconds and 6.47 GiB
maximum RSS. The complete execution obligation remains unproved.

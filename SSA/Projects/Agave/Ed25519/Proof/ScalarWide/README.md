# Scalar-wide reduction machine proof

The pinned `Scalar::from_bytes_mod_order_wide` has a complete linked RIR
execution proof. It reduces a 64-byte little-endian input to the canonical
32-byte scalar modulo
`L = 2^252 + 27742317777372353535851937790883648493`.
This is the subgroup scalar operation, distinct from the base-field `Reduce64`
kernel. The full invocation proof and its audit were committed in
`f3265219dbe1b610eacff66eccbb136fb91dead2` (`Complete scalar-wide reduction execution`).

## Checked endpoint and assumptions

Import `SSA.Projects.Agave.Ed25519.Proof.ScalarWide.FullCall` to obtain
`Agave.Ed25519.Verifier.Execution.ScalarWide.linked_program_call` and
`execution_obligation`. The former proves the actual call equation:

```lean
(linkedProgram g).call (args2 out input) state =
  .value (.nil, exactPostState state out bytes)
```

Its premises are `state.WF`, a live 32-byte output range, the original 64 input
bytes through `ReadBytes`, and invocation-local `Ready g state out`.
`Ready` requires the exact addresses and 40-byte initializers of R and RR,
distinct allocation ids for those globals, and an output allocation distinct
from both globals. It does not assume initialized globals in every state or
any callee execution equation.

`exactPostState` replaces exactly the 32 output bytes with `reducedBytes bytes`
and advances the allocation counter by 45. Those allocations comprise 24 in
the wrapper, nine plus one black-box allocation in each Montgomery call, and
one outer black-box allocation. All private allocations and scratch writes
are erased from the caller-visible memory. The output is the input integer
modulo L and is strictly less than L.

The stronger `linked_program_call` theorem does not require input/output
separation. `ExecutionObligation` and the ABI observation adapters retain the
explicit disjoint-range premise; it establishes preservation of the original
input bytes. `execution_obligation g` now supplies that obligation from the
machine proof. `Linked.lean` deliberately keeps its reusable adapters
parameterized by the obligation: instantiate
`observations_of_exact_execution` or `store_effect_of_exact_execution` with
`execution_obligation g`. The latter supplies SHA's exact `StoreEffect` and
preserves `Ready`. Global readiness remains a caller premise; this does not
assert `ReduceWideContract` for arbitrary uninitialized states.

## Proof structure

`ExecutionProgram.lean` imports both single-block bodies, and `Linked.lean`
binds the Montgomery and byte black-box calls to their extracted programs.
The wrapper has two Montgomery calls, one black-box call, 24 allocations,
11 fences, and two byte globals. The Montgomery body has one black-box call,
nine allocations, and nine fences.

- `ExecutionGlobals`, `Arithmetic`, and `GlobalOperands` identify R and RR as
  five radix-2^52 limbs representing `2^260 mod L` and `2^520 mod L`.
- The product, cancellation, carry, borrow, and addback modules prove the
  arithmetic and retained overflow/truncation flags of the actual word
  expressions. `MontgomeryWordCorrect.lean` proves
  `ScalarMontgomeryMul.montgomery_words_correct` for canonical modular output. `MontgomeryCall.lean` proves the complete
  `ScalarMontgomeryMul.program_call`, including five output stores, scratch
  erasure, and a counter increase of ten.
- The input and `Invocation*` modules derive mixed-width reads from the
  original 512-bit input, split at bit 260, instantiate both Montgomery calls
  with the exact globals, and compose the modular sum, serialization, output
  stores, and cleanup. Register values, live ranges, and scratch provenance
  are established along this execution.
- `InvocationReturn` proves exact final memory and counter behavior;
  `InvocationBody.lean` proves `invocation_body_run` over all instruction intervals;
  `FullCall.lean` applies the actual function-call frame rule. No whole-call or
  phase-execution premise is used as a replacement for this composition.

## Provenance and semantics boundary

The extraction/import manifests record no instruction normalization, body
rewrite, or extra inlining. The checked theorem uses the imported sequential
RIR semantics and its modeled instruction attributes. Extraction identity and
this execution proof do not by themselves prove a general LLVM-to-RIR
semantics theorem, compiler correctness, constant-time behavior, or
concurrent/volatile-event trace equivalence.

| Artifact | SHA-256 |
| --- | --- |
| Complete pinned crate LLVM | `2ea5bd097be748ddb48c0361700c0dacb5ee7146c87f29543001e78261c82dcc` |
| Wide LLVM | `3af5a470ac2ec4f002c3abf7ada62e1d02d18bf67bc1e247b8c21f5475ae582b` |
| Wide MLIR | `1f91ae907831e13b7c93d60549d03de6cbb40bf09ec376098cd9f50ebe700750` |
| Montgomery LLVM | `07f3f1e49ec2ea7470e3da8af1198f8f15eb1cb5ade67f652baa50173024ed79` |
| Montgomery MLIR | `2d0f10b723772e48d03534b067b4220829a86c9d1f254c1d63c44ed820678f48` |

[`scalar-wide-manifest.json`](../../MLIR/generated/scalar-wide-manifest.json)
records target symbols, original-definition hashes, LLVM 22.1.2 tools,
extraction commands, and operation inventories.
[`scalar-wide-rir-manifest.json`](../../MLIR/generated/scalar-wide-rir-manifest.json)
records exact region hashes, callees, globals, and importer-input hashes.

## Validation

On 2026-10-07, the final composition compiled on the devbox in
`/tmp/lmf-rir-ed25519-20261007` with Lean `nightly-2026-09-16`,
`lean -j1 --tstack=400000`, and normal-cache oleans. `FullCall` and
`FullCallAudit` passed in 5.672 and 5.322 seconds respectively.
`FullCallAudit.lean` checks 92 endpoints, including both full-call theorems,
and rejects dependencies outside `propext`, `Classical.choice`, and
`Quot.sound`. The closure uses no `sorry`, `admit`, added axioms,
`native_decide`, or `bv_decide` proof shortcut.

Session evidence is recorded in `/tmp/scalar-integration-all-results.json`,
`/tmp/scalar-integration-final-results.json`, and
`/tmp/scalar-integration-axioms.log`; devbox module logs are under
`/tmp/scalar-integration-logs/`. Current local source hashes were also checked against fresh devbox artifacts for `MontgomeryCall`,
`MontgomeryWordCorrect`, `InvocationReturn`, `InvocationBody`, `FullCall`, and
`FullCallAudit`, recorded in `/tmp/scalar-wide-readme-endpoints-20261007.json`.
Both extraction/import checks passed again. These session files are auxiliary
evidence; the committed sources, manifests, and guarded audit are the
reproducible proof boundary.

From a configured repository checkout on the devbox:

```sh
python3 SSA/Projects/Agave/Ed25519/MLIR/extract_scalar_wide.py --check
python3 SSA/Projects/Agave/Ed25519/MLIR/import_scalar_wide.py --check
lake build SSA.Projects.Agave.Ed25519.Proof.ScalarWide.FullCallAudit
```

# Mathematical correspondence audit

Research reference: [saymrwulf/anza-ed25519-verified](https://github.com/saymrwulf/anza-ed25519-verified/tree/cb0f1efc27db15f7896fce9423dfc76b4a69d1fa),
commit `cb0f1efc27db15f7896fce9423dfc76b4a69d1fa` (checked local HEAD),
commit author `mrwulf`.

No LICENSE, COPYING, NOTICE, or explicit license grant was found in the 92-file
tracked upstream snapshot. **No upstream code or comments are incorporated in
this directory.** The upstream proofs were research inspiration for identifying
useful mathematical obligations; the small local proofs were independently
written using Mathlib and the current Rust formulas. In particular the upstream
primality certificate and nonsquareness proof have not been copied. The current
Rust crate separately declares BSD-3-Clause; that declaration does not license
the upstream Lean code. `source-manifest.json` records this distinction and the
hashes of the research material and current Rust files examined.

## Locally proved statements and research correspondence

| Local file | Upstream research reference | Independent local result |
|---|---|---|
| `ToBytesMath.lean` | `Proofs/ToBytesMath.lean`: q facts, telescope, reduction | Fresh Presburger proofs of correction bit, exact canonicalization, five-carry telescope, weak-limb assembled bound. No byte-packing or machine-operation proof. |
| `EdwardsEncoding.lean` | `Proofs/PointEqSpec.lean`: coordinate/encoding injectivity | Generic field relation and odd-prime root parity; compression injectivity with **explicit** primality and nonzero-denominator premises. Concrete current D/SQRT_M1 integer congruence certificates. |
| `Canonicality.lean` | `Proofs/ScalarDenote.lean`: subgroup order | Natural-number equivalence of high-bit/reduction-equality parser and `s < ell`; independent y/sign packing and splitting. |
| `StrictSpec.lean` | Upstream apex audit and current strict Rust guards | Generic acceptance predicate retaining current guards; canonical-byte equality iff point equality under explicit encoding injectivity. |

Only Mathlib and the local pure field representation are imported. No Aeneas
model, custom axiom, `sorry`, `admit`, or `native_decide` is introduced.
`Audit.lean` prints the exported theorem axiom cones. Generic field/primality,
nonzero-denominator and encoding-injectivity premises are visible in theorem
statements; they are not silently instantiated for Ed25519. The directory does
not prove primality of the concrete modulus or nonsquareness of concrete d.

## Exact target and source comparison

The target examined is registry `solana-ed25519` **0.2.4**, whose
`.cargo_vcs_info.json` names commit
`33f07b22cb2fba719645052fdfc31d23bc917596`, path
`curve25519/solana-ed25519`. Hashes in `source-manifest.json` pin the actual
examined Rust files. This is not a claim that the upstream generated model was
extracted from that version. Upstream instead documents base commit `0a54cca`
and patched source `5f8e70e`, including a negate-then-assign decoding patch.
Those documented source pins are recorded, not independently re-extracted.
The upstream Aeneas project was inspected as source, not rebuilt or independently
certified by this audit. Only the independent local lemmas enter our build.

### FieldElement51

Current `src/backend/serial/u64/field.rs:364` computes exactly the mathematical
q telescope proved here: `(limb[0]+19)>>51`, then four additions and shifts;
it adds `19*q`, propagates carries and masks the final limb. Its own `h < 2p`
premise is also the premise of `canonicalize_eq_mod`. The current modulus and radix are unchanged. The current D and SQRT_M1
five-limb literals satisfy the defining modular relations, checked by
`current_d_limbs`, `current_d_relation` and `current_sqrt_m1_relation`.

**Not transferred:** upstream `fieldImplementation`, overflow/limb-bound
correctness for `reduce`, multiplication, inversion, or generated-function
specifications. They quantify over Aeneas `U64`/`Result` functions, not the
current local RIR or LLVM semantics. The arithmetic lemmas can discharge
mathematical obligations after a separate current-instruction refinement;
they do not supply that missing refinement themselves.

### Edwards decompression and compression

Current `src/edwards.rs:210–254` decodes y with `from_bytes`, obtains an even
root using `sqrt_ratio_i`, and conditionally negates it using bit 255.
Current `src/edwards/affine.rs:74–78` serializes canonical y and XORs x parity
into the top bit. These formulas motivate the independent generic field, root parity,
and injective encoding lemmas. Their prime and denominator hypotheses remain
explicit; upstream proofs discharging those hypotheses were not incorporated.

**Not transferred:** upstream `decompress_of_canonical` or any sqrt-ratio
execution theorem. The upstream theorem depends on its patched extraction
and proves canonical-input decoding, not arbitrary-input accept/reject
classification. The current conditional-negation implementation still needs
an instruction-level bridge. Noncanonical y and negative-zero sign aliases
must not silently be treated as canonical encodings: the local injectivity theorem is about canonical compression, with an explicit
canonical premise in `Strict.point_equation`.

### Scalar canonicality

Upstream `gen/CurveField/Funs.lean:4058–4070` uses a special
`check_scalar_canonical` bytewise less-than-ell loop followed by
`from_bytes_mod_order`. Current `src/scalar.rs:235–238` instead combines a
clear-high-bit test with `candidate.is_canonical()`; at line 1308 the latter
compares `self` with `self.reduce()`. The mathematical acceptance set is
`s < ell` if reduction and byte comparison are correct.
`scalarParserTest_iff` proves that mathematical fact. It does not prove
correctness of either machine parser, constant-time behavior, or the current
reduction implementation.

### Strict verification: upstream theorem does not transfer

Upstream `SigApexSpec.verify_accepts_iff` concerns the patched
`VerificationKey.verify_sha512`, fixes an all-zero-A filter and an encoded-R
blacklist through hypotheses, and assumes successful scalar parsing and
recomputation. Its axiom boundary additionally includes SHA-512 and foreign
signature accessors. The upstream README explicitly excludes default
Zebra/HEEA verification.

Current `src/ed_sigs/verification_key.rs:391–432` has a materially different
strict path: algebraic `minus_A.is_small_order()` rejection; R decompression;
algebraic `R.is_small_order()` rejection; canonical scalar parsing; and
recompute/compress byte equality. The source explicitly explains why an
encoding blacklist is not equivalent to these algebraic checks. The old
all-zero-A test also misses nonzero encodings of small-order points, including
the identity's canonical encoding. Therefore the old apex is **not** a strict
verification theorem for 0.2.4, even when renamed `verify_dalek`.

`StrictSpec.lean` preserves every current guard as an explicit mathematical
condition. Its point-equation theorem is conditional on encoding injectivity, **not a Rust/RIR/LLVM verifier refinement theorem**.
The small-order predicate, decoder result, challenge and recomputed point
still need concrete semantics/refinement. No hypothesis is hidden as an axiom.

Current default `verify()` at line 304 calls `verify_zebra`, which performs a
HEEA transformed, cofactored equation at lines 330–368. None of the local
lemmas proves that default verifier's acceptance criterion.

## Validation

Run from the Lean repository root, in this order:

```sh
lake build SSA.Projects.Agave.Ed25519.UpstreamMath.Audit
```

The aggregate imports all local independently written modules. Read the printed axiom
cones; no theorem is permitted to depend on `sorryAx`, a new custom axiom, or
an opaque external crypto function. Compilation establishes only the scopes
stated above. No regeneration or machine-code equivalence is claimed.

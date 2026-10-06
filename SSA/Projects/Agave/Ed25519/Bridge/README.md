# Ed25519 acceptance-policy bridge

The bridge shares Firedancer's existing `Edwards.Point Ed25519.curve` and proved
group operations. It does not introduce a second curve model or group axioms.

`Agave.Ed25519.Bridge.agave_iff_firedancer_and_canonical` in `Equivalence.lean`
states:

```text
AgaveStrictAccept a r s challenge
  ↔ FiredancerAccept a r s challenge ∧ CanonicalY r
```

There are no hypothesis arguments. `a` and `r` range over all 256-bit strings,
and `s` and `challenge` range over all natural numbers. `CanonicalY r` requires
the low 255 bits to be below `2^255 - 19`. The exceptional sign-bit ambiguity
at x = 0 cannot survive either client's small-order rejection.

The files establish these boundaries:

* `Encoding.lean`: concrete 256-bit compression, permissive decoding uniqueness,
  and exact compression equality for points with nonzero x.
* `SmallOrder.lean`: `8 • P = 0` iff P is in Firedancer's eight-coordinate list,
  proved using the existing curve group law.
* `Acceptance.lean`: acceptance predicates and the intermediate bridge with a
  named small-order correspondence premise.
* `Equivalence.lean`: discharges that premise; derives Agave acceptance implies
  Firedancer acceptance and equivalence for canonical R.
* `FiredancerSpec.lean`: checks definitionally that the encoding relation and
  scalar bound are those in the existing Firedancer verification specification;
  states the bridge with the original Firedancer definitions.
* `PolicyWitness.lean`: a noncanonical-R witness with shared challenge 1 that
  passes the Firedancer predicate and fails the Agave predicate. This is a
  specification-level witness, **not** a signature for a real message: no SHA-512
  preimage is provided or assumed.

This is an acceptance-specification theorem. To obtain a theorem about the two
executable validators, separately connect their implementations to these
predicates, and prove their SHA-512/scalar-reduction results coincide. The
explicit shared challenge keeps those obligations visible. Error-code equality
is not asserted.

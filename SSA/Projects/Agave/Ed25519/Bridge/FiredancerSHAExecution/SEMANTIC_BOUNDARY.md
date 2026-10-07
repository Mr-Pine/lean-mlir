# Common-digest semantic adapter

`DigestObservation.lean` composes the actual imported RIR initializer, three
linked appends (32-byte R, 32-byte A, machine-sized message), and linked finish.
Its observer checks the returned output pointer and output range, then reads
exactly the 512 output bits. The composition is a semantic runner, not a newly
extracted C/LLVM verifier body. The common specification is
`SHA512.digest SHA512.Spec.compression`, including padding and byte order.

`TranscriptInvocation.simulates_iff_digest` proves the exact remaining local
observation obligation. For an invocation `v` already proved `Correct r a msg`,

```
v.Simulates calls block offset r a msg
  ↔ firedancerDigest calls block offset r a msg =
      some (SHA512.digest SHA512.Spec.compression (hashTranscript r a msg))
```

No relation between RIR and SLLVM final states occurs on either side. The
forward implication suffices for the existing verifier proof; the reverse
implication demonstrates that the simulation demands no extra state facts.
Neither `Correct` nor `Simulates` is asserted for the pinned source here.

`ready_executionRefines_of_digest_simulation` in `SemanticAdapter.lean` (namespace
`Agave.Ed25519.Bridge.FiredancerSHAExecution`) feeds exactly that local digest
fact into `firedancerParameterized_ready_executionRefines`. It consumes the
existing source reducer result/value premises and proves the complete SLLVM
verifier execution/refinement at the common SHA-512 challenge. A uniform
`Challenge.DigestBy` premise is not necessary for this invocation-local result.
A separate conditional uniform transfer lemma is provided, but requires a
correct RIR invocation for every mathematical transcript; this is stronger
than machine-sized invocation correctness and is not supplied here.

## Exact remaining obligations

1. Prove `v.Correct r a msg` for the imported RIR calls under their real input,
   alias/range, constant-table and streaming-context conditions. The current
   source-loop and initializer leaves do not yet prove this entire chain.
2. Supply concrete `FiredancerShaPrograms` values of type **SLLVM.Cfg**, with
   `FiredancerShaInitBy`, `FiredancerShaAppendBy` and `FiredancerShaFinishBy`
   proofs for the chosen `calls`/`finishBlock`. These are local termination and
   SLLVM memory-frame contracts, including failure behavior, allocator/globals
   preservation, and the context/output block observations. They do not require
   cross-interpreter state equality. The imported **RIR.Func** values cannot
   inhabit this differently typed record. Digest equality alone also cannot
   establish these local footprints or manufacture the programs.
3. Prove `v.Simulates calls (some zeroed256ByteBlock) 0 r a msg` for the same
   invocation. A source-corresponding SLLVM import with a shared digest proof,
   or a sound local call adapter, can establish this. No theorem identifies
   the opaque legacy SHA CFG constants with the newly pinned source.

The new verifier endpoint has only the standard three Lean foundations in its
axiom closure, because all unresolved obligations above remain explicit
hypotheses. This is a conditional adapter and a precise remaining proof
boundary, not a completed removal of SHA hypotheses from concrete cross-client
execution. Source/compiler correspondence remains the import trust boundary.

# Pointwise verifier comparison

`CrossClientPointwiseDigest.lean` compares the Agave RIR wrapper with the
parameterized existing Firedancer verifier proof on the bytes read from one
actual invocation. Agave's SHA dispatcher and both scalar-multiplication
backends are fixed to their linked source implementations.

The digest premises concern just the current signature R, public key A and
message:

- `TranscriptInvocation.Correct` states that the imported Firedancer RIR SHA
  calls return the SHA-512 specification's digest for these bytes.
- `TranscriptInvocation.Simulates` states that this one observed 64-byte result
  agrees with the SLLVM SHA call composition used in the existing verifier proof.

There is no `Challenge.DigestBy` premise, universal machine representation of
arbitrary message lists, or equality of RIR and SLLVM memory states. The
pointwise Firedancer adapter also constructs the source reducer's return and
arithmetic witnesses from its universal checked proof.

The observation theorem preserves Agave's canonical-R check: its result is
Firedancer success conjoined with canonical R. The canonical-input corollary
removes that mask. The run variants construct both final states and actual
return-value equations, so the observation result cannot hold merely because
both computations fail. The reached R-decoder prefix remains guarded by successful
public-key decoding and continuation of the public-key small-order check.

The remaining boundaries are explicit: caller memory and loaded globals;
external hardware and bcmp instruction contracts; the decoder contract, caller
frame and reached prefix; the SLLVM SHA program contracts; and the two local
SHA digest observations above. This adapter does not prove those remaining
boundaries by treating an execution assumption as a source theorem.

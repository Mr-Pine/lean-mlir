# Concrete append observation refinement

`Append.Semantic.result_represents` closes the observation boundary of the
exact append proof. For an existing completed prefix and pending buffer, its
new ghost witnesses are exactly:

- completed: `completed ++ StreamSpec.complete (pending ++ chunk)`;
- pending: `StreamSpec.pending (pending ++ chunk)`.

Here `chunk` is read from the original input memory in address order.
`result_represents_exists` exposes their concatenation as the original
transcript followed by the chunk. `result_stream_represents` proves that the
returned memory satisfies the independent `StreamSpec.Represents` invariant.
`linked_call_represents` combines this result with the actual imported append
and scalar core call. It has no execution or compression-correctness premise.

The generic `result_rep` theorem starts from arbitrary chaining words and an
arbitrary 128-bit bit count. It proves the exact memory specification refines
`StreamSpec.append`, including the empty call, append fitting in the old
buffer, filling/compressing that buffer, arbitrary direct blocks, and both
zero/nonzero remainder paths. The proof checks little-endian native chaining
observations, copy offsets, exact pending count, preservation of the input
bytes, and the source's low/high counter carry.

The semantic result needs only the existing `ContextRepresents`, a live input
slice, and context/input allocation separation. The concrete execution
endpoint additionally uses the existing `Resources` contract (well-formed
state and the exact installed immutable constants). There is no bound on the
accumulated transcript length; the counter remains modulo 2^128. Individual
chunks obey the live-input bound required by the imported pointer arithmetic.
The existing `AppendZero.zero_call` also covers zero input with poison pointers
and without live-input or constant-table requirements.

`AppendSemanticAudit` checks all 31 semantic definitions and theorem endpoints
and rejects every transitive axiom except `propext`, `Classical.choice`, and
`Quot.sound`. The LLVM extraction/RIR semantic boundary remains the same as in
the concrete execution proof.

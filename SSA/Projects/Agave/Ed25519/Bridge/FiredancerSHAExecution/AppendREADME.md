# Firedancer SHA-512 append execution

`AppendLinked.linked_call` proves the public ABI of the actual imported
`Append.program` with the actual imported scalar `Core.program`. The result is
exactly `AppendModel.resultState`; no append/core execution equation is assumed.

The proof covers the empty return, nonempty counter update, append fitting in
an existing partial buffer, filling and compressing that buffer, arbitrary
positive direct block counts, and the trailing-byte copy. `resultState` gives
the exact sequence of counter stores, byte copies, common mathematical SHA-512
compression folds, and pending-count stores. Each compression call advances the
allocation counter once; its private scratch frame is erased. Append itself
allocates nothing.

`Resources` requires a well-formed initial state, a live 224-byte context, a live
input slice of `size.toNat` bytes, the exact installed constant initializer,
and context/input/constants allocation separation. The pending count must be
less than 128. A live input in `SmallRange` has size below 2^63, matching the
emitted signed inbounds pointer arithmetic. Word/counter arithmetic covers
64-bit wraparound. The separate `AppendZero.zero_call` needs only state
well-formedness: a zero-size call accepts arbitrary, even poison, pointers and
leaves the state unchanged.

The exact source-level model is a memory specification, not yet a theorem that
`ContextRepresents` is preserved for a whole transcript. That separate streaming
observation refinement can use `resultState` without re-proving control flow.
`linked_call_frame` proves the result is defined, the state is well formed,
all allocations other than the context are unchanged, and the constants remain
installed. `AppendAudit` rejects every transitive axiom other than `propext`,
`Classical.choice`, and `Quot.sound` across all 87 source/model/endpoints.

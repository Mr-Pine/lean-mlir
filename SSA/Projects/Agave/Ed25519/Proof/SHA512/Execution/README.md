# Imported SHA-512 finalizer execution

`FullCall.finalizer_contract` proves the existing
`Challenge.ScalarFromSha512Contract` for `SHA512Finalization.program.call`,
conditional on the local one-block compression contract and exact wide scalar
reduction contract. It executes the imported four-block function, including
its 70 allocations, context copy, one/two-block padding branch, eight serialized
u64 stores, reduction call, all 128 zeroizing byte stores, fences, lifetime
markers, return, and call-frame cleanup.

The length proof retains the original all-length context contract. The emitted
shifts and OR compute the bit length modulo 2^128, and the actual swapped length
store reads back as `SHA512.lengthField`. There is no additional 2^118 bound.
`SHA512.ByteOrder` connects the eight emitted byte-swapped words to the common
512-bit digest serialization.

For the concrete globally bound scalar reducer,
`linked_finalizer_of_execution` assumes `ScalarWide.ExecutionObligation g`
and preserves `ScalarWide.Ready g` from finalizer entry to the actual reducer
invocation. That obligation specifies the actual linked reducer call and its
exact post-state. It is still a premise: this finalizer proof does not establish
the Montgomery arithmetic or the wide reducer's body. Likewise, the concrete
SHA-512 compression implementation still needs its one-block contract.

`Audit.lean` checks the transitive axioms of the execution and composition
endpoints against only `propext`, `Classical.choice`, and `Quot.sound`. The proof
uses neither native reduction nor bit-vector decision-procedure certificates.

The source is split at actual instruction cutpoints: `Allocation` and `EntryTail`
compose in `Entry`; `BranchContracts` and padding readback compose in
`PaddedBranches`; `Serialization`, `Cutpoints`, and `FinalTail` compose in
`FinalBlock`; `FullCall` connects these and erases the private frame.

The `Cold*` modules add a contextual path for a compressor that may initialize
its designated one-byte CPU-feature cache. `CacheFrame` preserves every other
allocation exactly and records `CacheTransition`; `CacheOutputEffect` additionally
permits the expected output store. `ColdFullCall.finalizer_contract_cold` composes
the actual imported finalizer under `CompressionReady` and `ScalarWide.Ready`.
`finalizer_call_warm` recovers the exact output-only effect from a warm entry cache.

`ColdChallengeCall.challenge_call_cold` extends this to the actual challenge
prefix, bulk compression calls, context copy, finalizer, and return cleanup.
Its `ColdChallengeReady` states cache separation for the output, decoded key,
signature, message, and both Montgomery constants. The result includes the exact
challenge scalar and preservation of the caller's 192-byte key, 64-byte signature,
and message bytes. `coldLinked_finalizer_contract` links the imported finalizer
and wide reducer, retaining the compressor contract and the reducer's local
`ExecutionObligation`. `ColdAudit.lean` guards these endpoints separately.

The cold-cache modules through `ColdLinked` and the extended `ColdAudit` have
passed Lean validation, as has the existing `Audit`.
`ColdLinked.coldLinked_finalizer_contract_proved` instantiates the reducer
obligation with the proved `ScalarWide.execution_obligation`, leaving only the
local compressor contract. Its exact transitive axioms are `propext`,
`Classical.choice`, and `Quot.sound`. This closes scalar-reducer execution for
the linked cold finalizer; the concrete SHA compressor refinement remains a
separate obligation.

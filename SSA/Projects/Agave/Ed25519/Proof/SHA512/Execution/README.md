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

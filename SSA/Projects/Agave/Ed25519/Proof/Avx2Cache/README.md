# AVX2 cache initializer instruction boundary

`Contract.lean` provides `cache_contract` (namespace
`Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions`) proves the
Dalek caller's `CacheContract` for the extracted initializer CFG. It replaces
the former whole-call `CacheStoreExecution` assumption with explicit local
instruction contracts. `cache_call_normalized` additionally proves a 0/1 cache
byte and an unchanged allocation counter. All other memory reads outside the
cache byte and all previously live ranges are preserved.

The proof executes the real extracted control flow: three CPUID instructions,
the conditional XGETBV wrapper, bit masks/comparisons, Boolean conjunctions,
zero-extension, the byte store, and the return. The otherwise unused third
CPUID must still return successfully. Query results are arbitrary defined
bitvectors. No accuracy premise is needed for feature detection. The XGETBV
wrapper is itself imported and proved from its single intrinsic equation.

`LocalContract.lean` further narrows this interface to observations at one
invocation. `Local.Invocation` requires only the defined ECX field from
CPUID(1,0) and EBX field from CPUID(7,0). Every unused field, including the
entire CPUID(7,1) result, is arbitrary and may contain RIR poison. The third
instruction still has to terminate successfully and preserve the modeled
state. XGETBV(0) is required only when the source gate is true, and the store
equation concerns only the flag computed in this invocation, not both possible
bytes or any other address. `Local.initializer_call_framed` proves the exact
call, normalized cache byte, caller frame and unchanged allocation counter.
`Local.cache_contract` recovers the existing universal Dalek interface from
local witnesses only at its well-formed cold-cache caller states. The older
`InstructionContracts` implies this local interface by
`Local.of_instructionContracts`.

RIR currently rejects CPUID inline assembly, the XGETBV intrinsic, and atomic
stores. `MLIR/import_avx2_cache.py` therefore replaces only these instructions
with exactly typed raw effect bindings before using the normal RIR importer.
This is explicitly an **instruction-abstraction import**, not an unchanged
native RIR import or an unconditional proof of x86 semantics. The generated
`avx2-cache-instruction-manifest.json` records every original and replacement
instruction, source hashes, and the extraction-manifest hash. The script checks
the original MLIR hashes against that extraction manifest. No other operation
or branch changes; an explicit entry-block label is added for RIR syntax.

The remaining `InstructionContracts` obligations are:

- CPUID at `(1,0)`, `(7,0)`, and `(7,1)` returns defined register values without
  changing the sequential global state.
- XGETBV with input zero returns a defined 64-bit value without changing state,
  only when the first CPUID result passes the source XSAVE/OSXSAVE gate.
- The monotonic store of the computed 0/1 byte into a live one-byte range has
  exactly the corresponding sequential byte-store effect.

These are theorem parameters, not added axioms. Hardware legality, hardware
termination, and the interpretation of the atomic store remain explicit.
Concurrent atomic histories are outside this sequential model. Relating the
instruction bindings to the original LLVM operations remains a trusted
instruction-semantics boundary, recorded instead of hidden in a call equation.
The local interface does not remove these semantics assumptions: arbitrary
returned feature bits cannot establish that the gated XGETBV instruction is
legal or terminates. Query-state preservation describes RIR's memory and
allocation state only; it makes no assertion about unmodeled hardware state.

Run `python3 SSA/Projects/Agave/Ed25519/MLIR/import_avx2_cache.py --check` to
verify regeneration. Compile `InitializerProgram.lean`, `XgetbvProgram.lean`,
`Execution.lean`, `Contract.lean`, then `Audit.lean`. The audit checks that the
execution and caller-contract theorems depend only on `propext`,
`Classical.choice`, and `Quot.sound`; the explicit instruction parameters remain
visible in their theorem statements.
`LocalContract.lean` and `LocalAudit.lean` separately validate the five narrower
local proof endpoints against the same standard-axiom boundary.

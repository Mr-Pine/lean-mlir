# Source-corresponding SLLVM SHA calls

`SLLVMSourcePrograms.lean` supplies concrete `FiredancerShaPrograms` values
from the four scalar SHA regions pinned by `manifest.json` at Firedancer
`292f89b338a634e23e9f45c3dfdd5383ddcae624`. The actual verifier's SHA slots can
now use `SLLVMSource.programs` instead of arbitrary CFG parameters.

Run `python3 import_sllvm.py --check` from this directory to verify the original
artifact hashes and regenerate all four Lean module texts exactly. The importer
changes only legacy generic-parser spelling: numeric overflow flags to named
flags, opaque metadata payload quoting, empty integer-array spelling, and the
dotted global-symbol quoting. The compression callee in append and finish is
bound to the imported `SLLVMSource.core`.

## Checked endpoints

- `init_body` executes all eight IV stores and the 24-byte zeroing operation of
  the imported SLLVM initializer. It preserves all other bytes, including the
  buffer, magic field, and struct padding. It needs only a 224-byte context fit.
- `init_contract : FiredancerShaInitBy programs initModel` discharges the full
  existing verifier initializer contract. It proves return of the same pointer,
  allocator/global preservation, memory well-formedness, the context-block
  result, and unchanged other live allocations. Its only invocation premises
  are the contract's `WF` and 256-byte context fit.
- `init_call_observation_eq` compares two actual initializer calls, independently
  proved in SLLVM and RIR. It observes whether the original context pointer was
  returned and the complete resulting context allocation. Its premises are
  each input state's `WF`, SLLVM `Fits224`, RIR `SmallRange224`, equal input
  context bytes/length, and equal pointer offsets. Context block identifiers,
  globals, unrelated blocks, allocator counters, and final full states need not
  agree. Execution, return values, and output bytes are conclusions.
- `SLLVMSourceAudit.lean` checks the transitive axiom closure of the four CFG
  values, program bundle, and initializer endpoints against exactly the standard
  allowlist `propext`, `Classical.choice`, and `Quot.sound`.

The dependency order is Init, Core, Append, Finish, Programs, Initialize,
InitContract, InitObservation, Audit (all prefixed `SLLVMSource`).

## Remaining proof boundary

These modules do not prove SLLVM core, append, or finish execution. Therefore
`FiredancerShaAppendBy programs k appendModel`,
`FiredancerShaFinishBy programs k finishModel finishBlock`, and the actual
invocation's digest equality remain required by the verifier bridge. The
initializer can now be instantiated with `initModel` and `init_contract`.
Importing an identical source region is not a semantic RIR/SLLVM simulation.

A shortest sound next step is a narrow call relation that proves actual
append/finalizer return, written context/output blocks, unchanged caller blocks,
and allocator/global restoration from their reachable stream invariants. The
single-store byte relation `rir_storeAt_block` and initializer observation give
a checked starting point. RIR's frame cleanup erases private blocks while SLLVM
marks them dead and restores the entry allocation counter, so a full-state
equality would be unnecessary and generally false.

The existing uniform `Sha512AppendBy` and `Sha512FiniBy` contracts also quantify
malformed or unreachable contexts and inputs up to the 64-bit bound. Existing
RIR linked-call theorems use `SmallRange` and initialized pending-count/stream
facts. Instantiating those uniform contracts needs proofs for their larger
domain; alternatively specialize the verifier proof to the reachable call
sequence. Do not replace the larger-domain obligations with an assumed digest
observation equality.

The original C-to-LLVM-to-MLIR extraction and imported-region interpretation
remain trusted boundaries. SLLVM intentionally ignores GEP `inbounds`/no-wrap
metadata, load/store alignment, and alias metadata; this is visible in its
parser. The initializer cross-dialect theorem uses RIR's stronger `SmallRange`
premise and proves only the stated defined executions. No native/compiler
semantic preservation theorem, full-stream SHA theorem, SHA assembly theorem,
or correspondence between the older verifier lift and the newly pinned SHA
source version is asserted here.

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

## Complete reachable calls

The imported core, append, and finalizer now have direct SLLVM execution
proofs. They do not rely on an RIR/SLLVM interpreter simulation:

- `Core.executes` proves arbitrary positive compression block counts with raw
  initialized K bytes, small live ranges, separation, and complete caller framing.
- The `SLLVMAppend*` modules prove the R32/A32 prefix and arbitrary message
  append, preserving the completed/pending stream representation.
- `MessageExecution.reachable_message` proves an exact context block result
  independent of input allocation identity, supplying the verifier's third
  reachable append contract.
- `FinishCorrect.call_digest_source` and `reachable_finish_source` prove both
  finalization branches, the standard transcript digest, and the output frame.
- `verifierTailCalls` instantiates the message-append and finalizer contracts;
  `CrossClientReachableConcrete` and `CrossClientLoaded` compose them with the
  actual verifier. No SHA call or digest-equality premise remains there.

The older uniform `FiredancerShaAppendBy`/`FiredancerShaFinishBy` interfaces
quantify over additional malformed contexts. The closed comparison instead
uses the exact reachable init/R/A/message/finalizer sequence. Generalizing to
unreachable contexts is unnecessary for this verifier theorem.

Strict transitive audits for the core, append, finalizer, adapters, and final
comparison admit only `propext`, `Classical.choice`, and `Quot.sound`. The
complete checks and source/artifact provenance are recorded in the
[parent proof ledger](../ProofClosureLedger.md).

## Interpretation boundary

The original C-to-LLVM-to-MLIR extraction and imported-region interpretation
remain trusted boundaries. SLLVM ignores GEP `inbounds`/no-wrap metadata,
load/store alignment, and alias metadata; explicit arithmetic overflow flags
remain in the imported instructions. Small-allocation assumptions prove the
addresses used by the executed paths. RIR frame cleanup erases private blocks;
SLLVM marks them dead and restores the entry allocation counter. The proofs
compare the relevant observations, not entire interpreter states.

No native/compiler refinement, accelerated Firedancer SHA assembly theorem,
or source-version identity between the older verifier lift and the newly
pinned SHA region is asserted. The final result is the source-linked imported
verifier's defined acceptance behavior, with the canonical-R policy explicit.

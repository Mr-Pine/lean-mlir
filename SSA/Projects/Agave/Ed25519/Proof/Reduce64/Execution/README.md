# Reduce64 execution bridge

The complete staged execution and readback bridge passed direct Lean validation
through `Audit.lean` on 2026-10-07, using the pinned toolchain. The guarded
`kernel_call`, `outputWord_storeOutputs`, and `kernel_correct` checks report only
`propext`, `Classical.choice`, and `Quot.sound`.

- `Memory.lean`: caller memory ranges imply every load/store fits, offsets do
  not wrap, and the live small-allocation GEP predicate holds.
- `Packing.lean`: actual RIR bitcast and shuffle semantics; poison halves are
  discarded, and the physical 8×32-bit order is related to `Word.reduce`.
- `Step.lean`: stepping support for a state-reading inbounds GEP.
- `Output.lean`: the five stores and pure output-register/limb readback, without
  importing the exact kernel proof. Downstream field proofs can use it directly.
- `StageTypes.lean`: the live constants and word-register facts at each cut.
- `StageConstants.lean`: instructions `[0,54)`, the constant and poison setup.
- `StageCarryA.lean`: instructions `[54,67)`, the first two independent carries.
- `StageCarryB.lean`: instructions `[67,85)`, the remaining low/high carry chains.
- `StageFold.lean`: instructions `[85,106)`, the final carries and multiplication
  by 19, including all arithmetic overflow flags.
- `StagePacking.lean`: instructions `[106,129)`, bitcasts, poison masks, shuffles.
- `StageStores.lean`: instructions `[129,138)`, the five stores and four GEPs.
- `Kernel.lean`: composes these separate lemmas into the actual `program.call`
  equality, retaining the original memory-to-memory theorem signatures.
- `Readback.lean`: composes actual execution with integer-limb and field-residue
  correctness.
- `Audit.lean`: guarded axiom checks for the execution and readback endpoints.

The wrapping execution theorem has no arithmetic input bound. The integer and
residue endpoint uses the existing per-lane `ColumnsBound`. The memory premise
`SmallRange` names a live block smaller than 2^63 bytes and requires the complete
320-byte input or 160-byte output interval to lie inside it. `GlobalState.WF`
justifies call-frame cleanup. No nonalias hypothesis is needed by RIR execution
because all ten loads precede all five stores. LLVM alias metadata and physical
allocation alignment remain obligations of the source-to-RIR validity contract.

The current translator retains the complete `inbounds nusw nuw` semantics for
constant GEPs. Every emitted address calculation is a state-reading step whose
live allocation, offset arithmetic, and within-object conditions are discharged
from `SmallRange`.

The stage interfaces use continuations for the memory-preserving prefix. Each
proof executes only its own instruction interval and passes explicit register
facts to the next proof. The final memory effect has a separate nine-instruction
lemma. A static coverage check confirms 138 steps over contiguous intervals;
this source consistency check supplements the validated composition in `Kernel.lean`.

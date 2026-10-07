# Ordinary memory attributes at the LLVM/RIR boundary

The current execution theorems establish RIR results and memory frames. They do
not establish LLVM alignment or volatile-event equivalence. This audit records
that residual explicitly and supplies checked alignment arithmetic; it does not
change any production program or execution theorem.

## What is erased

In `SSA/Projects/RIR/Syntax/Translate.lean`, `instr` maps an ordinary
`llvm.load` to `.load` at line 716 and `llvm.store` to `.store` at line 729.
Neither branch reads `alignment` or `volatile_`. `checkNotAtomic` at lines
484–488 only checks the ordering. The monotonic-byte-load branch at lines
717–721 separately rejects volatile/syncscope modifiers. `alloca` at lines
742–755 retains the allocation size, but not the alignment.

`Instruction.lean:100,106` has no alignment or volatility field on ordinary
load/store. `Semantics/Operations/Memory.lean:15–44` checks pointer poison and
`Fits`, and stores also check value poison. `Memory/Pointer.lean:11–19` represents
a pointer by allocation ID and byte offset. `Semantics/Effectful/Memory/Fits.lean:10–11` checks only
allocation existence and bounds. `Proof/Reduce64/Execution/Memory.lean:11–12`
adds a small-allocation bound in `SmallRange`, not address alignment.

`Translation.lean` proves by kernel reduction that changing align 1 to align
128 leaves these imported instructions identical, and that adding `volatile_`
also leaves them identical. These are witnesses of the present importer,
not refinement lemmas licensing those LLVM changes. Source comments saying all
flags are retained, such as `ScalarReduce32/Program.lean:10`, refer at most to
the quoted source text; they are too broad if read as claims about RIR semantics.

LLVM requires each load/store address to satisfy its stated alignment; an
overestimate causes undefined behavior. Align 1 imposes no extra restriction.
Volatile accesses may have target-specific side effects, and their number and
relative ordering matter. Thus erasing volatility needs a restricted observation
and a target/environment condition. See the [LLVM 22.1 load/store reference](https://releases.llvm.org/22.1.0/docs/LangRef.html#load-instruction)
and [volatile rules](https://releases.llvm.org/22.1.0/docs/LangRef.html#volatile-memory-accesses).

## Exact inventory and affected bodies

`inventory.json` records source hashes, line numbers, block names, zero-based
source operation indices, full access text, and syntactic pointer roots.
`python3 SSA/Projects/Agave/Ed25519/Proof/SourceMemoryAudit/inventory.py --check`
rechecks it. It covers all direct `execution_def`, `mlir_def`, and `mlir_region%`
bodies under Ed25519 `Proof` and `Bridge/FiredancerSHAExecution`, excluding this
audit's synthetic witnesses. It checks that no quoted load/store/alloca in that
scope escaped the parser. Observation slices and alternate/duplicated CFG
presentations are included: these counts are not a reachable call graph or
dynamic execution counts.

The snapshot has 63 files, 104 definitions, 366 allocas, 876 loads, and 1,276
stores. Three loads are monotonic atomic bytes; 873 are ordinary. Every recorded
access/allocation has explicit alignment. The following table accounts for all
96 volatile loads and 173 volatile stores; line references are relative to
`SSA/Projects/Agave/Ed25519/Proof`.

| Imported body | Volatile loads / stores | Exact first site | Syntactic pointer roots |
| --- | ---: | --- | --- |
| `Encoding/DecompressExecution/BlackBoxProgram.lean` | 1 / 0 | line 19, `%2 = load %1`, align 1 | private alloca |
| `ScalarReduce32/Program.lean` | 10 / 23 | line 209, `store %21, %72`, align 8 | private allocas; align 8/16 |
| `ScalarWide/ExecutionProgram.lean`, first body | 5 / 13 | line 450, `store %46, %76`, align 8 | private allocas |
| `ScalarWide/ExecutionProgram.lean`, Montgomery body | 0 / 9 | line 935, `store %23, %24`, i128 align 16 | private allocas |
| `SHA512/ExecutionProgram.lean` | 0 / 128 | line 341, `store %8, %87`, i8 align 1 | private allocas |
| `SHA512/Compression/DispatchProgram.lean` | 80 / 0 | line 296, `%258 = load %23`, i64 align 8 | SHA K constant global |

These are actual source markers: LLVM counterparts include
`MLIR/generated/agave_subtle_black_box.ll:11`,
`agave_scalar_montgomery_mul.ll:247`,
`agave_scalar_from_sha512.ll:241`, and
`agave_sha512_compress_dispatch.ll:118`. The latter loads K[0]; the following
volatile load at line 145 reads K[1] at byte offset 8. The inventory traces only
syntactic GEP/bitcast chains, not arbitrary PHI provenance. All volatile sites
in this snapshot resolve to the roots shown above.

The four new Firedancer SHA bodies contain 29 loads, 33 stores, and one alloca,
with no volatile or atomic operations. Agave AVX2 SHA also has no volatile
loads/stores. The verifier wrapper/Dalek bodies themselves have no volatile
accesses; their imported callees listed above do. The existing
`Verifier/DalekBlackBoxPrimitive.lean:12–13` already limits its result to returned
value and sequential memory frame.

## Concrete alignment obligations

All LLVM files below are under the corresponding project's `generated` directory.

| Body and exact evidence | Sufficient address condition |
| --- | --- |
| Firedancer `fd_sha512_init.ll:9–23`: stores at offsets 128,136,144,152,160,168,176,184 with alignments 128,8,16,8,32,8,16,8 | context address divisible by 128 |
| Firedancer `fd_sha512_append.ll:16,26`, `fd_sha512_fini.ll:15`: context+208 has align 16 | context divisible by 16; the API's 128-byte alignment suffices |
| Firedancer `fd_sha512_fini.ll:45,50,55,60,65,70,75,80`: eight output stores, all align 8 | output address divisible by 8 |
| Firedancer `fd_sha512_core_ref.ll:18–25`: state words align 8; line 54: input word align 1; line 10: scratch alloca align 16; line 6: K global align 16 | state divisible by 8, source-aligned scratch/K bases, arbitrary input-byte alignment |
| Agave `agave_sha512_compress_avx2.ll:9–13`: chain argument align 8 and three private allocas align 16 | chain divisible by 8 and source-aligned stack bases |
| Agave `Compression/Avx2Program.lean:365–478`, bb9: 16 input vector loads align 1 and 16 scratch/cache stores align 16 | arbitrary input-byte alignment; scratch/cache divisible by 16, stores at 16*i |

The checked lemmas `firedancer_init_stores_aligned`, `firedancer_counter_aligned`,
`sha_words_aligned`, `avx2_initial_pair_store_aligned`, and
`avx2_group_store_aligned` discharge these offset calculations from the base
conditions and existing `SmallRange` bounds. They also cover cache offsets
128*group + 16*pair. They do not silently infer a base address from an allocation
ID. `ByteGlobal.Present` already documents this distinction in `RIR/Global.lean:15`.

In particular, Firedancer `Initialize.lean:56–58,96` assumes only `SmallRange`
for the context. `ContextRepresents.live` also has no alignment field.
`firedancer_init_range_does_not_imply_alignment` constructs a live 224-byte
context at offset 1 in a 256-byte allocation whose base is 128. Its first store
would address byte 257, violating LLVM align 128. Thus the existing RIR theorem
admits states outside the LLVM-defined domain. This is not evidence that a
properly constructed C context is misaligned: the pinned Firedancer header
defines `FD_SHA512_ALIGN` as 128 and footprint as 256. The RIR live-range size
224 describes accessed bytes; it is not the complete C allocation contract.
The emitted Finish output alignment 8 must likewise be explicit when connecting
its byte-buffer theorem to these LLVM stores.

## Minimal residual for this audit

For a proposed machine realization of a proved RIR run, require:

1. **Per-access alignment:** at every executed source ordinary load/store with
   declared alignment A and RIR pointer p, A divides `base(p.id) + p.offset`.
   Realization also supplies the already separate address validity/nonoverlap
   conditions. Source-aligned stack/global bases and appropriately aligned
   arguments, together with the checked offset lemmas, discharge many instances.
2. **Volatile value/memory behavior:** the listed volatile sites access ordinary
   RAM with no interference; each volatile load returns the current bytes and
   each volatile store has the modeled byte update, without additional effects
   on the selected observations. K is stable; private allocations are private.
   Compare return values and the stated memory observations after projecting
   away volatile events. No volatile-event trace, physical erasure/zeroization,
   MMIO, signal-handler, or concurrent-history theorem follows.

These are local source-semantics conditions, not a premise that the whole
decoder, verifier, or SHA function executes correctly. No extra axiom is added
to Lean. In particular, “no volatile accesses” would be false for this corpus.
An event-preserving source theorem would require extending the semantics and
tracking those events; private-frame erasure cannot establish it.

This audit does not discharge the separate compiler/import trust boundary,
function/call attributes, alias/TBAA promises, lifetime/uninitialized-memory
refinement, or memcpy/memset attributes. Atomic cache ownership remains the
separate existing sequential-execution restriction. Ordinary alignment and
volatile conditions must be included alongside those existing boundaries,
rather than describing current RIR execution theorems as full LLVM equivalence.

## Validation

`Alignment.lean`, `Translation.lean`, and `Audit.lean` were checked on the devbox
with pinned Lean 4.36.0-nightly-2026-09-16, one `-j1` process at a time and explicit
`.olean` outputs. All three passed without warnings. `Audit.lean` reports that
all 14 theorems use only subsets of `propext`, `Classical.choice`, and `Quot.sound`.
The exact
checked source hashes, command, and audit output are supplied in the task's
validation manifest; inventory source hashes are independent of proof checks.

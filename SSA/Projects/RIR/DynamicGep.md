# Dynamic GEP support

The new `Instr.gep` models **unflagged** LLVM `getelementptr` for RIR's default
address space and 64-bit pointer index type. It supports any number of scalar
integer indices, arrays, vectors and constant structure selectors. Each dynamic
integer is sign-extended or truncated to 64 bits before scaling. Scaling, offset
addition and addition to the pointer offset wrap modulo 2^64. Poison in either
the base or any index poisons the result. Computing a pointer does not load
memory or raise immediate UB. Subsequent loads/stores keep their existing
allocation and extent checks.

Sequential indices may be negative or outside the array/vector type's declared
length; LLVM permits this, including indices into zero-length array types.
Structure selectors must be constant and in range. The layout is the existing
RIR `Ty.sizeAlign` layout; other address spaces, pointer index widths and target
data layouts remain outside this importer.

The importer resolves `rawConstantIndices` dynamic sentinels against SSA
operands. An operand defined by `llvm.mlir.constant` is folded using its declared
signed integer width. Flags are checked before any constant folding. Supported
flagged constants use `Instr.gepInbounds`, retaining all allocation and overflow
checks; unsupported flag combinations reject even when every index is constant.
Only genuinely unflagged indices accepted by `gepOffset` use the existing
`UnOp.gepConst` path. This preserves those legacy unflagged lifts; it is not a
new soundness claim for their overflow behavior.

## Rejected forms and proof boundary

The exact LLVM 22 combination `noWrapFlags = 7 : i32` (`inbounds nusw nuw`) has
a separate effectful `Instr.gepInbounds` lift. It looks up the allocation, checks
signed and unsigned index truncation/scaling, signed cumulative offsets, and
every intermediate address including the base and one-past endpoint. Negative
byte steps poison the result: when remaining in the same allocation, unsigned
addition of the sign-extended negative offset necessarily wraps. Independent
`nusw`, `nuw`, other dynamic flag combinations and `inrange` remain rejected.

This lift is restricted to allocations currently represented in `MemoryState`
and smaller than 2^63 bytes. Missing allocations produce a poison result. LLVM
can allow some GEPs on dead objects, so the live-allocation premise is required
for a refinement claim; this is not an unconditional model of dangling-pointer
formation. Failures produce a poison pointer rather than immediate UB, so a
subsequent use such as a load/store is still necessary to trigger UB.

`Semantics/Operations/InboundsGep.lean` proves conditional result equalities under
explicit allocation lookup, size, signed arithmetic and intermediate-address
premises. It also proves that nonnegative in-object steps cannot overflow a
concrete machine address when the entire allocation has a non-wrapping
placement, and that backwards steps violate the combined `nuw` flag. Installed
globals satisfy the same allocation lookup through `ByteGlobal.Present`.

RIR's pointer contains a block identifier and an offset; it has no concrete
allocation base address. Its memory map also erases freed stack allocations.
LLVM's `inbounds` allows a pointer into a deallocated object (including its
one-past address), checks intermediate addresses, and implies `nusw` arithmetic
requirements. Checking only the current live block's size therefore poisons
some LLVM-defined executions outside the stated live-object domain. Full support needs retained
allocation provenance/extents and an adequate address/no-wrap model, or a
separately proved restriction to a domain where these checks coincide. The
restriction above must be discharged by clients; successful import alone does
not establish it.

See the [LLVM GEP semantics](https://llvm.org/docs/LangRef.html#getelementptr-instruction)
and [GEP FAQ](https://llvm.org/docs/GetElementPtr.html). Focused regression tests
are in `Tests/Syntax/DynamicGep.lean` and `Tests/Syntax/InboundsGep.lean`.

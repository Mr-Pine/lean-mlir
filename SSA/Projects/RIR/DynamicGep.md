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
signed integer width. If the resulting index list is accepted by the existing
`gepOffset`, it uses the existing `UnOp.gepConst` path. This preserves existing
constant-GEP lifts and their proof contracts. In particular, this is **not** a
repair or a new soundness claim for the legacy constant GEP handling of flags
or overflow.

## Rejected forms and proof boundary

Genuinely dynamic or newly supported signed GEPs with `inbounds`, `nusw`, `nuw`
or `inrange` are rejected, including the MLIR `noWrapFlags` spelling. They are
not silently treated as unflagged instructions.

RIR's pointer contains a block identifier and an offset; it has no concrete
allocation base address. Its memory map also erases freed stack allocations.
LLVM's `inbounds` allows a pointer into a deallocated object (including its
one-past address), checks intermediate addresses, and implies `nusw` arithmetic
requirements. Checking only the current live block's size would therefore
incorrectly poison some LLVM-defined executions. Full support needs retained
allocation provenance/extents and an adequate address/no-wrap model, or a
separately proved restriction to a domain where these checks coincide. No such
restriction is implicitly assumed by this change.

See the [LLVM GEP semantics](https://llvm.org/docs/LangRef.html#getelementptr-instruction)
and [GEP FAQ](https://llvm.org/docs/GetElementPtr.html). Focused regression tests
are in `Tests/Syntax/DynamicGep.lean`.

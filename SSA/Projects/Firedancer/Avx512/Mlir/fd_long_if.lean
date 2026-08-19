/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# `fd_long_if`, lifted from Firedancer's AVX-512 ed25519 implementation

The program below is the MLIR translation of `fd_long_if` from
`firedancer/src/util/bits/fd_bits.h`, taken **verbatim** from the build
artifact `build/native/gcc/mlir/avx512/region/fd_long_if.mlir`. Nothing is
rewritten -- not the generic-form `llvm.icmp`, not the `fastmathFlags` the
`select` carries.

`%4` is the result.

## Why it is a region at all, and why it takes one argument

`fd_long_if(c,t,f)` is `c ? t : f`, branchless for deterministic timing. It is
a `static inline`, so in a real build it disappears into a `cmov`; it survives
here only because `make mlir-avx512` passes `-fno-inline` to keep each
`fd_r43x6_*` operation in its own region.

What the compiler emitted is therefore not the general three-argument
function. `fd_long_if` is `static`, so it has internal linkage and LLVM can see
every call to it in the translation unit; the only one is
`fd_r43x6_mod_nearly_reduced_limbs`'s `fd_long_if( !_c, 19L, 0L )`. IPSCCP
replaces a parameter that takes the *same constant at every call site* with
that constant in the body, and dead-argument elimination then drops the
now-unused parameter. So the region takes only the condition, and the `0` and
`19` it selects between are literals inside it.

Measured, not assumed, on `clang-18 -O2 -fno-inline`: two call sites passing
*different* constants leave all three parameters in place; two passing the same
constants specialise exactly as one does; and a parameter constant at one site
but variable at another survives while its constant neighbour is folded. The
condition is agreement across call sites, per parameter -- having a single call
site merely satisfies it trivially.

This shape is therefore stable as more probes are added. Every expansion of
`fd_r43x6_mod_nearly_reduced_limbs` passes the same two literals, so lifting
`fd_r43x6_mod` or `fd_r43x6_pack` alongside would add call sites that agree and
leave this region unchanged.

That is why `Spec/fd_long_if.lean` specifies `c ? 19 : 0` rather than
`fd_long_if`'s documented meaning: this region *is* the specialisation, and
proving anything else about it would be proving something about a program that
does not exist.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM

/-- The region as an AST value, so it can be written once and used both as the
`Com` below and as the callee binding in `Mlir/fd_r43x6_is_nonzero.lean`. -/
def fd_long_ifRegion : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: i32):
    %0 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %3 = "llvm.icmp"(%arg0, %0) <{predicate = 0 : i64}> : (i32, i32) -> i1
    %4 = "llvm.select"(%3, %1, %2) <{fastmathFlags = #llvm.fastmath<none>}> : (i1, i64, i64) -> i64
    "llvm.return"(%4) : (i64) -> ()
}]

def fd_long_if := [sllvm_of| fd_long_ifRegion]

end Firedancer.Avx512

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Avx512.Mlir.fd_long_if

/-!
# `fd_r43x6_is_nonzero`, lifted from Firedancer's AVX-512 ed25519 implementation

All four of the blockers this file was once checked in to *display* are gone:
`llvm.extractelement` had no operation at all and stopped the region at `%14`
(`LIMITATIONS.md` 7.2); generic-form `llvm.icmp` stopped it at `%58` (6.5); and
the `llvm.call` at `%60` had nothing to call, because `Com` has no symbol table
(4.1). The call is now an operation carrying its callee as a region, and
`with @fd_long_if := fd_long_ifRegion` is what binds it -- MLIR's `llvm.call`
names a symbol and carries no inline region, so the body has to be supplied.

There are now **no deviations at all**: what follows is byte-for-byte the
artifact. The last one to go was the `nsw` quoting (6.1) -- while `nsw` was a
reserved token, every flag had to be rewritten before it could be quoted.

The program below is the MLIR translation of `fd_r43x6_is_nonzero` from
`firedancer/src/ballet/ed25519/avx512/fd_r43x6.h`, taken from the build
artifact `build/native/gcc/mlir/avx512/region/fd_r43x6_is_nonzero.mlir`, which
is checked in beside this file **verbatim** -- the `.mlir` and the region below
differ in nothing but indentation. Its one callee is
`Avx512/Mlir/fd_long_if.lean`, likewise verbatim, and proven in
`Avx512/Proof/fd_long_if.lean`.

`%79` is the result, the `i32` the C returns.

## What the region does

`%14`-`%19` are `fd_r43x6_extract_limbs`: the six limbs off the `<8 x i64>`.
`%20`-`%38` are `fd_r43x6_biased_carry_propagate_limbs` at `b = 2^20`, and
`%39`-`%71` are `fd_r43x6_mod_nearly_reduced_limbs`. `%72`-`%79` are the
`!!(l0|l1|l2|l3|l4|l5)` read off the end.

Two things the compiler did that the proof will have to follow:

* `%72`-`%77` OR the *unmasked* `e0`-`e4` and mask once (`%76 = (e0|e1|e2|e3|e4)
  & m43`), rather than ORing the masked limbs `z0`-`z4`. Same answer, one fewer
  `and` per limb.
* `%58` is `icmp ult %56, 2^40` where the source asks whether `a5 >> 40` is
  zero, and `%60` is a call to a `fd_long_if` that constant propagation has
  already specialised to `select(%59 == 0, 0, 19)`.

Every arithmetic operation here carries `nsw`, and the `mod_nearly_reduced`
half carries `nuw` on top of it. lean-mlir's `LLVM.add` yields poison on signed
overflow, so this region does not denote to a value at all without the input
range `CarryPre` of `Spec/fd_r43x6_is_nonzero.lean`.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM

/-- `fd_r43x6_is_nonzero`, as the compiler emits it: the six limb extracts, both
carry chains, and the call at `%60` still a call. -/
def fd_r43x6_is_nonzero := [sllvm|
  {
    ^bb0(%arg0: vector<8xi64>):
      %0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
      %1 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
      %2 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
      %3 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
      %4 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
      %5 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
      %6 = "llvm.mlir.constant"() <{value = -1048576 : i64}> : () -> i64
      %7 = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
      %8 = "llvm.mlir.constant"() <{value = 1099511627775 : i64}> : () -> i64
      %9 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
      %10 = "llvm.mlir.constant"() <{value = 43 : i64}> : () -> i64
      %11 = "llvm.mlir.constant"() <{value = 8796093022207 : i64}> : () -> i64
      %12 = "llvm.mlir.constant"() <{value = 1048576 : i64}> : () -> i64
      %13 = "llvm.mlir.constant"() <{value = 1099511627776 : i64}> : () -> i64
      %14 = "llvm.extractelement"(%arg0, %0) : (vector<8xi64>, i64) -> i64
      %15 = "llvm.extractelement"(%arg0, %1) : (vector<8xi64>, i64) -> i64
      %16 = "llvm.extractelement"(%arg0, %2) : (vector<8xi64>, i64) -> i64
      %17 = "llvm.extractelement"(%arg0, %3) : (vector<8xi64>, i64) -> i64
      %18 = "llvm.extractelement"(%arg0, %4) : (vector<8xi64>, i64) -> i64
      %19 = "llvm.extractelement"(%arg0, %5) : (vector<8xi64>, i64) -> i64
      %20 = "llvm.add"(%19, %6) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
      %21 = "llvm.ashr"(%20, %7) : (i64, i64) -> i64
      %22 = "llvm.and"(%20, %8) : (i64, i64) -> i64
      %23 = "llvm.mul"(%21, %9) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
      %24 = "llvm.add"(%23, %14) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
      %25 = "llvm.ashr"(%24, %10) : (i64, i64) -> i64
      %26 = "llvm.and"(%24, %11) : (i64, i64) -> i64
      %27 = "llvm.add"(%25, %15) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
      %28 = "llvm.ashr"(%27, %10) : (i64, i64) -> i64
      %29 = "llvm.and"(%27, %11) : (i64, i64) -> i64
      %30 = "llvm.add"(%28, %16) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
      %31 = "llvm.ashr"(%30, %10) : (i64, i64) -> i64
      %32 = "llvm.and"(%30, %11) : (i64, i64) -> i64
      %33 = "llvm.add"(%31, %17) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
      %34 = "llvm.ashr"(%33, %10) : (i64, i64) -> i64
      %35 = "llvm.and"(%33, %11) : (i64, i64) -> i64
      %36 = "llvm.add"(%34, %18) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
      %37 = "llvm.ashr"(%36, %10) : (i64, i64) -> i64
      %38 = "llvm.and"(%36, %11) : (i64, i64) -> i64
      %39 = "llvm.add"(%26, %9) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
      %40 = "llvm.lshr"(%39, %10) : (i64, i64) -> i64
      %41 = "llvm.and"(%39, %11) : (i64, i64) -> i64
      %42 = "llvm.add"(%29, %40) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
      %43 = "llvm.lshr"(%42, %10) : (i64, i64) -> i64
      %44 = "llvm.and"(%42, %11) : (i64, i64) -> i64
      %45 = "llvm.add"(%32, %43) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
      %46 = "llvm.lshr"(%45, %10) : (i64, i64) -> i64
      %47 = "llvm.and"(%45, %11) : (i64, i64) -> i64
      %48 = "llvm.add"(%35, %46) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
      %49 = "llvm.lshr"(%48, %10) : (i64, i64) -> i64
      %50 = "llvm.and"(%48, %11) : (i64, i64) -> i64
      %51 = "llvm.add"(%38, %49) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
      %52 = "llvm.lshr"(%51, %10) : (i64, i64) -> i64
      %53 = "llvm.and"(%51, %11) : (i64, i64) -> i64
      %54 = "llvm.add"(%22, %12) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
      %55 = "llvm.add"(%54, %37) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
      %56 = "llvm.add"(%55, %52) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
      %57 = "llvm.and"(%56, %8) : (i64, i64) -> i64
      %58 = "llvm.icmp"(%56, %13) <{predicate = 6 : i64}> : (i64, i64) -> i1
      %59 = "llvm.zext"(%58) : (i1) -> i32
      %60 = "llvm.call"(%59) <{CConv = #llvm.cconv<fastcc>, callee = @fd_long_if, fastmathFlags = #llvm.fastmath<none>}> : (i32) -> i64
      %61 = "llvm.sub"(%41, %60) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
      %62 = "llvm.ashr"(%61, %10) : (i64, i64) -> i64
      %63 = "llvm.add"(%62, %44) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
      %64 = "llvm.ashr"(%63, %10) : (i64, i64) -> i64
      %65 = "llvm.add"(%64, %47) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
      %66 = "llvm.ashr"(%65, %10) : (i64, i64) -> i64
      %67 = "llvm.add"(%66, %50) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
      %68 = "llvm.ashr"(%67, %10) : (i64, i64) -> i64
      %69 = "llvm.add"(%68, %53) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
      %70 = "llvm.ashr"(%69, %10) : (i64, i64) -> i64
      %71 = "llvm.add"(%70, %57) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
      %72 = "llvm.or"(%63, %61) : (i64, i64) -> i64
      %73 = "llvm.or"(%72, %65) : (i64, i64) -> i64
      %74 = "llvm.or"(%73, %67) : (i64, i64) -> i64
      %75 = "llvm.or"(%74, %69) : (i64, i64) -> i64
      %76 = "llvm.and"(%75, %11) : (i64, i64) -> i64
      %77 = "llvm.or"(%76, %71) : (i64, i64) -> i64
      %78 = "llvm.icmp"(%77, %0) <{predicate = 1 : i64}> : (i64, i64) -> i1
      %79 = "llvm.zext"(%78) : (i1) -> i32
      "llvm.return"(%79) : (i32) -> ()
  }
with @fd_long_if := fd_long_ifRegion]

end Firedancer.Avx512

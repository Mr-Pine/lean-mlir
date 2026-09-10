/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Common.Mlir.fd_ulong_load_8

/-!
# `fd_curve25519_scalar_reduce` (common)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/{ref,avx512}/region/fd_curve25519_scalar_reduce.mlir`.
The two backends' regions are the same file, as is the one callee
`fd_ulong_load_8`, so the function is lifted once, here -- as
`fd_curve25519_scalar_validate` is.

`fd_curve25519_scalar.c`: reduce a 512-bit little-endian scalar mod the group
order `l = 2^252 + 27742317777372353535851937790883648493`, writing 32 bytes.
`%arg0` is `out`, `%arg1` is `in`; the region returns `%arg0`.

One block, and entirely straight-line: 51 constants, then eight
`fd_ulong_load_8` calls reading `in` at 0, 8, ..., 56, then the unpacking into
twenty-four 21-bit digits, the reduction proper, and four `i64` stores through
`out` at 0, 8, 16, 24.

The seven `llvm.intr.fshl` are the digits that straddle a word boundary: the C
writes `(in0>>63) | (in1<<1)` and the compiler contracts each to one funnel
shift.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM

-- 498 lines in one block: the quotation's own recursion, not the proof's.
set_option maxRecDepth 100000 in
def fd_curve25519_scalar_reduce_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 48 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 56 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 2097151 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 21 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 42 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 20 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 41 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %15 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %16 = "llvm.mlir.constant"() <{value = 18 : i64}> : () -> i64
    %17 = "llvm.mlir.constant"() <{value = 39 : i64}> : () -> i64
    %18 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %19 = "llvm.mlir.constant"() <{value = 17 : i64}> : () -> i64
    %20 = "llvm.mlir.constant"() <{value = 38 : i64}> : () -> i64
    %21 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %22 = "llvm.mlir.constant"() <{value = 37 : i64}> : () -> i64
    %23 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %24 = "llvm.mlir.constant"() <{value = 15 : i64}> : () -> i64
    %25 = "llvm.mlir.constant"() <{value = 36 : i64}> : () -> i64
    %26 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %27 = "llvm.mlir.constant"() <{value = 14 : i64}> : () -> i64
    %28 = "llvm.mlir.constant"() <{value = 35 : i64}> : () -> i64
    %29 = "llvm.mlir.constant"() <{value = 666643 : i64}> : () -> i64
    %30 = "llvm.mlir.constant"() <{value = 470296 : i64}> : () -> i64
    %31 = "llvm.mlir.constant"() <{value = 654183 : i64}> : () -> i64
    %32 = "llvm.mlir.constant"() <{value = -997805 : i64}> : () -> i64
    %33 = "llvm.mlir.constant"() <{value = 136657 : i64}> : () -> i64
    %34 = "llvm.mlir.constant"() <{value = -683901 : i64}> : () -> i64
    %35 = "llvm.mlir.constant"() <{value = 1048576 : i64}> : () -> i64
    %36 = "llvm.mlir.constant"() <{value = 8796090925056 : i64}> : () -> i64
    %37 = "llvm.mlir.constant"() <{value = -2097152 : i64}> : () -> i64
    %38 = "llvm.mlir.constant"() <{value = 4398044413952 : i64}> : () -> i64
    %39 = "llvm.mlir.constant"() <{value = 9223367638808264704 : i64}> : () -> i64
    %40 = "llvm.mlir.constant"() <{value = 63 : i64}> : () -> i64
    %41 = "llvm.mlir.constant"() <{value = 1048575 : i64}> : () -> i64
    %42 = "llvm.mlir.constant"() <{value = 2199022206976 : i64}> : () -> i64
    %43 = "llvm.mlir.constant"() <{value = 4611683819404132352 : i64}> : () -> i64
    %44 = "llvm.mlir.constant"() <{value = 62 : i64}> : () -> i64
    %45 = "llvm.mlir.constant"() <{value = 524287 : i64}> : () -> i64
    %46 = "llvm.mlir.constant"() <{value = 1099511103488 : i64}> : () -> i64
    %47 = "llvm.mlir.constant"() <{value = 2305841909702066176 : i64}> : () -> i64
    %48 = "llvm.mlir.constant"() <{value = 61 : i64}> : () -> i64
    %49 = "llvm.mlir.constant"() <{value = 262143 : i64}> : () -> i64
    %50 = "llvm.mlir.constant"() <{value = 549755551744 : i64}> : () -> i64
    %51 = "llvm.call"(%arg1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_load_8, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i64
    %52 = "llvm.getelementptr"(%arg1, %0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %53 = "llvm.call"(%52) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_load_8, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i64
    %54 = "llvm.getelementptr"(%arg1, %1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %55 = "llvm.call"(%54) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_load_8, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i64
    %56 = "llvm.getelementptr"(%arg1, %2) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %57 = "llvm.call"(%56) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_load_8, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i64
    %58 = "llvm.getelementptr"(%arg1, %3) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %59 = "llvm.call"(%58) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_load_8, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i64
    %60 = "llvm.getelementptr"(%arg1, %4) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %61 = "llvm.call"(%60) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_load_8, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i64
    %62 = "llvm.getelementptr"(%arg1, %5) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %63 = "llvm.call"(%62) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_load_8, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i64
    %64 = "llvm.getelementptr"(%arg1, %6) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %65 = "llvm.call"(%64) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_load_8, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i64
    %66 = "llvm.and"(%51, %7) : (i64, i64) -> i64
    %67 = "llvm.lshr"(%51, %8) : (i64, i64) -> i64
    %68 = "llvm.and"(%67, %7) : (i64, i64) -> i64
    %69 = "llvm.lshr"(%51, %9) : (i64, i64) -> i64
    %70 = "llvm.and"(%69, %7) : (i64, i64) -> i64
    %71 = "llvm.intr.fshl"(%53, %51, %10) : (i64, i64, i64) -> i64
    %72 = "llvm.and"(%71, %7) : (i64, i64) -> i64
    %73 = "llvm.lshr"(%53, %11) : (i64, i64) -> i64
    %74 = "llvm.and"(%73, %7) : (i64, i64) -> i64
    %75 = "llvm.lshr"(%53, %12) : (i64, i64) -> i64
    %76 = "llvm.and"(%75, %7) : (i64, i64) -> i64
    %77 = "llvm.intr.fshl"(%55, %53, %13) : (i64, i64, i64) -> i64
    %78 = "llvm.and"(%77, %7) : (i64, i64) -> i64
    %79 = "llvm.lshr"(%55, %14) : (i64, i64) -> i64
    %80 = "llvm.and"(%79, %7) : (i64, i64) -> i64
    %81 = "llvm.lshr"(%55, %4) : (i64, i64) -> i64
    %82 = "llvm.and"(%81, %7) : (i64, i64) -> i64
    %83 = "llvm.intr.fshl"(%57, %55, %15) : (i64, i64, i64) -> i64
    %84 = "llvm.and"(%83, %7) : (i64, i64) -> i64
    %85 = "llvm.lshr"(%57, %16) : (i64, i64) -> i64
    %86 = "llvm.and"(%85, %7) : (i64, i64) -> i64
    %87 = "llvm.lshr"(%57, %17) : (i64, i64) -> i64
    %88 = "llvm.and"(%87, %7) : (i64, i64) -> i64
    %89 = "llvm.intr.fshl"(%59, %57, %18) : (i64, i64, i64) -> i64
    %90 = "llvm.and"(%89, %7) : (i64, i64) -> i64
    %91 = "llvm.lshr"(%59, %19) : (i64, i64) -> i64
    %92 = "llvm.and"(%91, %7) : (i64, i64) -> i64
    %93 = "llvm.lshr"(%59, %20) : (i64, i64) -> i64
    %94 = "llvm.and"(%93, %7) : (i64, i64) -> i64
    %95 = "llvm.intr.fshl"(%61, %59, %21) : (i64, i64, i64) -> i64
    %96 = "llvm.and"(%95, %7) : (i64, i64) -> i64
    %97 = "llvm.lshr"(%61, %1) : (i64, i64) -> i64
    %98 = "llvm.and"(%97, %7) : (i64, i64) -> i64
    %99 = "llvm.lshr"(%61, %22) : (i64, i64) -> i64
    %100 = "llvm.and"(%99, %7) : (i64, i64) -> i64
    %101 = "llvm.intr.fshl"(%63, %61, %23) : (i64, i64, i64) -> i64
    %102 = "llvm.and"(%101, %7) : (i64, i64) -> i64
    %103 = "llvm.lshr"(%63, %24) : (i64, i64) -> i64
    %104 = "llvm.and"(%103, %7) : (i64, i64) -> i64
    %105 = "llvm.lshr"(%63, %25) : (i64, i64) -> i64
    %106 = "llvm.and"(%105, %7) : (i64, i64) -> i64
    %107 = "llvm.intr.fshl"(%65, %63, %26) : (i64, i64, i64) -> i64
    %108 = "llvm.and"(%107, %7) : (i64, i64) -> i64
    %109 = "llvm.lshr"(%65, %27) : (i64, i64) -> i64
    %110 = "llvm.and"(%109, %7) : (i64, i64) -> i64
    %111 = "llvm.lshr"(%65, %28) : (i64, i64) -> i64
    %112 = "llvm.mul"(%111, %29) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %113 = "llvm.add"(%112, %88) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %114 = "llvm.mul"(%111, %30) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %115 = "llvm.add"(%114, %90) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %116 = "llvm.mul"(%111, %31) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %117 = "llvm.add"(%116, %92) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %118 = "llvm.mul"(%111, %32) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %119 = "llvm.add"(%118, %94) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %120 = "llvm.mul"(%111, %33) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %121 = "llvm.add"(%120, %96) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %122 = "llvm.mul"(%111, %34) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %123 = "llvm.add"(%122, %98) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %124 = "llvm.mul"(%110, %29) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %125 = "llvm.mul"(%110, %30) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %126 = "llvm.mul"(%110, %31) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %127 = "llvm.mul"(%110, %32) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %128 = "llvm.mul"(%110, %33) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %129 = "llvm.add"(%119, %128) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %130 = "llvm.mul"(%110, %34) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %131 = "llvm.add"(%121, %130) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %132 = "llvm.mul"(%108, %29) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %133 = "llvm.mul"(%108, %30) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %134 = "llvm.mul"(%108, %31) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %135 = "llvm.mul"(%108, %32) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %136 = "llvm.mul"(%108, %33) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %137 = "llvm.mul"(%108, %34) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %138 = "llvm.add"(%129, %137) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %139 = "llvm.mul"(%106, %29) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %140 = "llvm.add"(%139, %82) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %141 = "llvm.mul"(%106, %30) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %142 = "llvm.mul"(%106, %31) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %143 = "llvm.mul"(%106, %32) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %144 = "llvm.mul"(%106, %33) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %145 = "llvm.mul"(%106, %34) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %146 = "llvm.mul"(%104, %29) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %147 = "llvm.add"(%146, %80) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %148 = "llvm.mul"(%104, %30) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %149 = "llvm.add"(%140, %148) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %150 = "llvm.mul"(%104, %31) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %151 = "llvm.mul"(%104, %32) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %152 = "llvm.mul"(%104, %33) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %153 = "llvm.mul"(%104, %34) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %154 = "llvm.add"(%115, %144) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %155 = "llvm.add"(%154, %153) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %156 = "llvm.add"(%155, %126) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %157 = "llvm.add"(%156, %135) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %158 = "llvm.mul"(%102, %29) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %159 = "llvm.add"(%158, %78) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %160 = "llvm.mul"(%102, %30) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %161 = "llvm.add"(%147, %160) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %162 = "llvm.mul"(%102, %31) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %163 = "llvm.add"(%149, %162) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %164 = "llvm.mul"(%102, %32) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %165 = "llvm.mul"(%102, %33) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %166 = "llvm.add"(%142, %86) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %167 = "llvm.add"(%166, %151) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %168 = "llvm.add"(%167, %165) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %169 = "llvm.add"(%168, %124) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %170 = "llvm.add"(%169, %133) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %171 = "llvm.mul"(%102, %34) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %172 = "llvm.add"(%159, %35) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %173 = "llvm.lshr"(%172, %8) : (i64, i64) -> i64
    %174 = "llvm.add"(%161, %173) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %175 = "llvm.and"(%172, %36) : (i64, i64) -> i64
    %176 = "llvm.sub"(%159, %175) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %177 = "llvm.add"(%163, %35) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %178 = "llvm.lshr"(%177, %8) : (i64, i64) -> i64
    %179 = "llvm.add"(%141, %84) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %180 = "llvm.add"(%179, %150) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %181 = "llvm.add"(%180, %164) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %182 = "llvm.add"(%181, %132) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %183 = "llvm.add"(%182, %178) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %184 = "llvm.and"(%177, %37) : (i64, i64) -> i64
    %185 = "llvm.sub"(%163, %184) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %186 = "llvm.add"(%170, %35) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %187 = "llvm.ashr"(%186, %8) : (i64, i64) -> i64
    %188 = "llvm.add"(%113, %143) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %189 = "llvm.add"(%188, %152) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %190 = "llvm.add"(%189, %171) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %191 = "llvm.add"(%190, %125) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %192 = "llvm.add"(%191, %134) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %193 = "llvm.add"(%192, %187) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %194 = "llvm.and"(%186, %37) : (i64, i64) -> i64
    %195 = "llvm.add"(%157, %35) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %196 = "llvm.ashr"(%195, %8) : (i64, i64) -> i64
    %197 = "llvm.add"(%117, %145) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %198 = "llvm.add"(%197, %127) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %199 = "llvm.add"(%198, %136) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %200 = "llvm.add"(%199, %196) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %201 = "llvm.and"(%195, %37) : (i64, i64) -> i64
    %202 = "llvm.sub"(%157, %201) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %203 = "llvm.add"(%138, %35) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %204 = "llvm.ashr"(%203, %8) : (i64, i64) -> i64
    %205 = "llvm.add"(%131, %204) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %206 = "llvm.and"(%203, %37) : (i64, i64) -> i64
    %207 = "llvm.sub"(%138, %206) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %208 = "llvm.add"(%123, %35) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %209 = "llvm.ashr"(%208, %8) : (i64, i64) -> i64
    %210 = "llvm.add"(%209, %100) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %211 = "llvm.and"(%208, %37) : (i64, i64) -> i64
    %212 = "llvm.sub"(%123, %211) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %213 = "llvm.add"(%174, %35) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %214 = "llvm.lshr"(%213, %8) : (i64, i64) -> i64
    %215 = "llvm.and"(%213, %37) : (i64, i64) -> i64
    %216 = "llvm.add"(%183, %35) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %217 = "llvm.ashr"(%216, %8) : (i64, i64) -> i64
    %218 = "llvm.and"(%216, %37) : (i64, i64) -> i64
    %219 = "llvm.add"(%193, %35) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %220 = "llvm.ashr"(%219, %8) : (i64, i64) -> i64
    %221 = "llvm.add"(%220, %202) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %222 = "llvm.and"(%219, %37) : (i64, i64) -> i64
    %223 = "llvm.sub"(%193, %222) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %224 = "llvm.add"(%200, %35) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %225 = "llvm.ashr"(%224, %8) : (i64, i64) -> i64
    %226 = "llvm.add"(%225, %207) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %227 = "llvm.and"(%224, %37) : (i64, i64) -> i64
    %228 = "llvm.sub"(%200, %227) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %229 = "llvm.add"(%205, %35) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %230 = "llvm.ashr"(%229, %8) : (i64, i64) -> i64
    %231 = "llvm.add"(%230, %212) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %232 = "llvm.and"(%229, %37) : (i64, i64) -> i64
    %233 = "llvm.sub"(%205, %232) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %234 = "llvm.mul"(%210, %29) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %235 = "llvm.add"(%234, %76) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %236 = "llvm.mul"(%210, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %237 = "llvm.add"(%176, %236) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %238 = "llvm.mul"(%210, %31) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %239 = "llvm.mul"(%210, %32) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %240 = "llvm.mul"(%210, %33) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %241 = "llvm.mul"(%210, %34) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %242 = "llvm.add"(%170, %241) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %243 = "llvm.sub"(%242, %194) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %244 = "llvm.add"(%243, %217) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %245 = "llvm.mul"(%231, %29) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %246 = "llvm.add"(%245, %74) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %247 = "llvm.mul"(%231, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %248 = "llvm.add"(%235, %247) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %249 = "llvm.mul"(%231, %31) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %250 = "llvm.add"(%237, %249) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %251 = "llvm.mul"(%231, %32) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %252 = "llvm.mul"(%231, %33) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %253 = "llvm.mul"(%231, %34) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %254 = "llvm.mul"(%233, %29) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %255 = "llvm.add"(%254, %72) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %256 = "llvm.mul"(%233, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %257 = "llvm.add"(%246, %256) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %258 = "llvm.mul"(%233, %31) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %259 = "llvm.add"(%248, %258) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %260 = "llvm.mul"(%233, %32) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %261 = "llvm.add"(%250, %260) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %262 = "llvm.mul"(%233, %33) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %263 = "llvm.mul"(%233, %34) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %264 = "llvm.add"(%185, %239) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %265 = "llvm.add"(%264, %214) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %266 = "llvm.add"(%265, %252) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %267 = "llvm.add"(%266, %263) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %268 = "llvm.mul"(%226, %29) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %269 = "llvm.add"(%268, %70) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %270 = "llvm.mul"(%226, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %271 = "llvm.add"(%255, %270) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %272 = "llvm.mul"(%226, %31) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %273 = "llvm.add"(%257, %272) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %274 = "llvm.mul"(%226, %32) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %275 = "llvm.add"(%259, %274) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %276 = "llvm.mul"(%226, %33) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %277 = "llvm.add"(%261, %276) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %278 = "llvm.mul"(%226, %34) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %279 = "llvm.mul"(%228, %29) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %280 = "llvm.add"(%279, %68) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %281 = "llvm.mul"(%228, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %282 = "llvm.add"(%269, %281) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %283 = "llvm.mul"(%228, %31) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %284 = "llvm.add"(%271, %283) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %285 = "llvm.mul"(%228, %32) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %286 = "llvm.add"(%273, %285) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %287 = "llvm.mul"(%228, %33) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %288 = "llvm.add"(%275, %287) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %289 = "llvm.mul"(%228, %34) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %290 = "llvm.add"(%277, %289) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %291 = "llvm.mul"(%221, %29) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %292 = "llvm.add"(%291, %66) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %293 = "llvm.mul"(%221, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %294 = "llvm.add"(%280, %293) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %295 = "llvm.mul"(%221, %31) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %296 = "llvm.add"(%282, %295) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %297 = "llvm.mul"(%221, %32) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %298 = "llvm.add"(%284, %297) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %299 = "llvm.mul"(%221, %33) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %300 = "llvm.add"(%286, %299) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %301 = "llvm.mul"(%221, %34) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %302 = "llvm.add"(%288, %301) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %303 = "llvm.add"(%292, %35) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %304 = "llvm.ashr"(%303, %8) : (i64, i64) -> i64
    %305 = "llvm.add"(%294, %304) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %306 = "llvm.and"(%303, %37) : (i64, i64) -> i64
    %307 = "llvm.sub"(%292, %306) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %308 = "llvm.add"(%296, %35) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %309 = "llvm.ashr"(%308, %8) : (i64, i64) -> i64
    %310 = "llvm.add"(%298, %309) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %311 = "llvm.and"(%308, %37) : (i64, i64) -> i64
    %312 = "llvm.sub"(%296, %311) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %313 = "llvm.add"(%300, %35) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %314 = "llvm.ashr"(%313, %8) : (i64, i64) -> i64
    %315 = "llvm.add"(%302, %314) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %316 = "llvm.and"(%313, %37) : (i64, i64) -> i64
    %317 = "llvm.sub"(%300, %316) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %318 = "llvm.add"(%290, %35) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %319 = "llvm.ashr"(%318, %8) : (i64, i64) -> i64
    %320 = "llvm.add"(%238, %174) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %321 = "llvm.sub"(%320, %215) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %322 = "llvm.add"(%321, %251) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %323 = "llvm.add"(%322, %262) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %324 = "llvm.add"(%323, %278) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %325 = "llvm.add"(%324, %319) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %326 = "llvm.and"(%318, %37) : (i64, i64) -> i64
    %327 = "llvm.sub"(%290, %326) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %328 = "llvm.add"(%267, %35) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %329 = "llvm.ashr"(%328, %8) : (i64, i64) -> i64
    %330 = "llvm.add"(%183, %240) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %331 = "llvm.sub"(%330, %218) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %332 = "llvm.add"(%331, %253) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %333 = "llvm.add"(%332, %329) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %334 = "llvm.and"(%328, %37) : (i64, i64) -> i64
    %335 = "llvm.sub"(%267, %334) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %336 = "llvm.add"(%244, %35) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %337 = "llvm.ashr"(%336, %8) : (i64, i64) -> i64
    %338 = "llvm.add"(%337, %223) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %339 = "llvm.and"(%336, %37) : (i64, i64) -> i64
    %340 = "llvm.sub"(%244, %339) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %341 = "llvm.add"(%305, %35) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %342 = "llvm.ashr"(%341, %8) : (i64, i64) -> i64
    %343 = "llvm.and"(%341, %37) : (i64, i64) -> i64
    %344 = "llvm.add"(%310, %35) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %345 = "llvm.ashr"(%344, %8) : (i64, i64) -> i64
    %346 = "llvm.and"(%344, %37) : (i64, i64) -> i64
    %347 = "llvm.add"(%315, %35) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %348 = "llvm.ashr"(%347, %8) : (i64, i64) -> i64
    %349 = "llvm.add"(%327, %348) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %350 = "llvm.and"(%347, %37) : (i64, i64) -> i64
    %351 = "llvm.add"(%325, %35) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %352 = "llvm.ashr"(%351, %8) : (i64, i64) -> i64
    %353 = "llvm.add"(%335, %352) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %354 = "llvm.and"(%351, %37) : (i64, i64) -> i64
    %355 = "llvm.sub"(%325, %354) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %356 = "llvm.add"(%333, %35) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %357 = "llvm.ashr"(%356, %8) : (i64, i64) -> i64
    %358 = "llvm.add"(%340, %357) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %359 = "llvm.and"(%356, %37) : (i64, i64) -> i64
    %360 = "llvm.sub"(%333, %359) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %361 = "llvm.add"(%338, %35) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %362 = "llvm.ashr"(%361, %8) : (i64, i64) -> i64
    %363 = "llvm.and"(%361, %37) : (i64, i64) -> i64
    %364 = "llvm.sub"(%338, %363) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %365 = "llvm.mul"(%362, %29) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %366 = "llvm.add"(%307, %365) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %367 = "llvm.mul"(%362, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %368 = "llvm.mul"(%362, %31) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %369 = "llvm.mul"(%362, %32) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %370 = "llvm.mul"(%362, %33) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %371 = "llvm.mul"(%362, %34) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %372 = "llvm.ashr"(%366, %8) : (i64, i64) -> i64
    %373 = "llvm.add"(%367, %305) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %374 = "llvm.sub"(%373, %343) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %375 = "llvm.add"(%374, %372) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %376 = "llvm.and"(%366, %7) : (i64, i64) -> i64
    %377 = "llvm.ashr"(%375, %8) : (i64, i64) -> i64
    %378 = "llvm.add"(%312, %368) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %379 = "llvm.add"(%378, %342) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %380 = "llvm.add"(%379, %377) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %381 = "llvm.and"(%375, %7) : (i64, i64) -> i64
    %382 = "llvm.ashr"(%380, %8) : (i64, i64) -> i64
    %383 = "llvm.add"(%310, %369) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %384 = "llvm.sub"(%383, %346) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %385 = "llvm.add"(%384, %382) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %386 = "llvm.and"(%380, %7) : (i64, i64) -> i64
    %387 = "llvm.ashr"(%385, %8) : (i64, i64) -> i64
    %388 = "llvm.add"(%317, %370) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %389 = "llvm.add"(%388, %345) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %390 = "llvm.add"(%389, %387) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %391 = "llvm.and"(%385, %7) : (i64, i64) -> i64
    %392 = "llvm.ashr"(%390, %8) : (i64, i64) -> i64
    %393 = "llvm.add"(%315, %371) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %394 = "llvm.sub"(%393, %350) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %395 = "llvm.add"(%394, %392) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %396 = "llvm.and"(%390, %7) : (i64, i64) -> i64
    %397 = "llvm.ashr"(%395, %8) : (i64, i64) -> i64
    %398 = "llvm.add"(%349, %397) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %399 = "llvm.and"(%395, %7) : (i64, i64) -> i64
    %400 = "llvm.ashr"(%398, %8) : (i64, i64) -> i64
    %401 = "llvm.add"(%400, %355) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %402 = "llvm.and"(%398, %7) : (i64, i64) -> i64
    %403 = "llvm.ashr"(%401, %8) : (i64, i64) -> i64
    %404 = "llvm.add"(%353, %403) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %405 = "llvm.and"(%401, %7) : (i64, i64) -> i64
    %406 = "llvm.ashr"(%404, %8) : (i64, i64) -> i64
    %407 = "llvm.add"(%406, %360) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %408 = "llvm.and"(%404, %7) : (i64, i64) -> i64
    %409 = "llvm.ashr"(%407, %8) : (i64, i64) -> i64
    %410 = "llvm.add"(%358, %409) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %411 = "llvm.and"(%407, %7) : (i64, i64) -> i64
    %412 = "llvm.ashr"(%410, %8) : (i64, i64) -> i64
    %413 = "llvm.add"(%412, %364) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %414 = "llvm.and"(%410, %7) : (i64, i64) -> i64
    %415 = "llvm.ashr"(%413, %8) : (i64, i64) -> i64
    %416 = "llvm.and"(%413, %7) : (i64, i64) -> i64
    %417 = "llvm.mul"(%415, %29) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %418 = "llvm.add"(%417, %376) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %419 = "llvm.mul"(%415, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %420 = "llvm.add"(%419, %381) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %421 = "llvm.mul"(%415, %31) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %422 = "llvm.add"(%421, %386) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %423 = "llvm.mul"(%415, %32) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %424 = "llvm.add"(%423, %391) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %425 = "llvm.mul"(%415, %33) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %426 = "llvm.add"(%425, %396) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %427 = "llvm.mul"(%415, %34) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %428 = "llvm.add"(%427, %399) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %429 = "llvm.ashr"(%418, %8) : (i64, i64) -> i64
    %430 = "llvm.add"(%420, %429) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %431 = "llvm.and"(%418, %7) : (i64, i64) -> i64
    %432 = "llvm.ashr"(%430, %8) : (i64, i64) -> i64
    %433 = "llvm.add"(%422, %432) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %434 = "llvm.ashr"(%433, %8) : (i64, i64) -> i64
    %435 = "llvm.add"(%424, %434) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %436 = "llvm.ashr"(%435, %8) : (i64, i64) -> i64
    %437 = "llvm.add"(%426, %436) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %438 = "llvm.ashr"(%437, %8) : (i64, i64) -> i64
    %439 = "llvm.add"(%428, %438) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %440 = "llvm.ashr"(%439, %8) : (i64, i64) -> i64
    %441 = "llvm.add"(%440, %402) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %442 = "llvm.ashr"(%441, %8) : (i64, i64) -> i64
    %443 = "llvm.add"(%442, %405) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %444 = "llvm.ashr"(%443, %8) : (i64, i64) -> i64
    %445 = "llvm.add"(%444, %408) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %446 = "llvm.ashr"(%445, %8) : (i64, i64) -> i64
    %447 = "llvm.add"(%446, %411) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %448 = "llvm.ashr"(%447, %8) : (i64, i64) -> i64
    %449 = "llvm.add"(%448, %414) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %450 = "llvm.ashr"(%449, %8) : (i64, i64) -> i64
    %451 = "llvm.add"(%450, %416) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %452 = "llvm.shl"(%430, %8) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %453 = "llvm.and"(%452, %38) : (i64, i64) -> i64
    %454 = "llvm.or"(%453, %431) : (i64, i64) -> i64
    %455 = "llvm.shl"(%433, %9) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %456 = "llvm.and"(%455, %39) : (i64, i64) -> i64
    %457 = "llvm.or"(%454, %456) : (i64, i64) -> i64
    %458 = "llvm.shl"(%435, %40) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %459 = "llvm.or"(%457, %458) : (i64, i64) -> i64
    "llvm.store"(%459, %arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %460 = "llvm.lshr"(%435, %10) : (i64, i64) -> i64
    %461 = "llvm.and"(%460, %41) : (i64, i64) -> i64
    %462 = "llvm.shl"(%437, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %463 = "llvm.and"(%462, %42) : (i64, i64) -> i64
    %464 = "llvm.or"(%463, %461) : (i64, i64) -> i64
    %465 = "llvm.shl"(%439, %12) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %466 = "llvm.and"(%465, %43) : (i64, i64) -> i64
    %467 = "llvm.or"(%464, %466) : (i64, i64) -> i64
    %468 = "llvm.shl"(%441, %44) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %469 = "llvm.or"(%467, %468) : (i64, i64) -> i64
    %470 = "llvm.getelementptr"(%arg0, %0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%469, %470) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %471 = "llvm.lshr"(%441, %13) : (i64, i64) -> i64
    %472 = "llvm.and"(%471, %45) : (i64, i64) -> i64
    %473 = "llvm.shl"(%443, %14) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %474 = "llvm.and"(%473, %46) : (i64, i64) -> i64
    %475 = "llvm.or"(%474, %472) : (i64, i64) -> i64
    %476 = "llvm.shl"(%445, %4) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %477 = "llvm.and"(%476, %47) : (i64, i64) -> i64
    %478 = "llvm.or"(%475, %477) : (i64, i64) -> i64
    %479 = "llvm.shl"(%447, %48) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %480 = "llvm.or"(%478, %479) : (i64, i64) -> i64
    %481 = "llvm.getelementptr"(%arg0, %1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%480, %481) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %482 = "llvm.lshr"(%447, %15) : (i64, i64) -> i64
    %483 = "llvm.and"(%482, %49) : (i64, i64) -> i64
    %484 = "llvm.shl"(%449, %16) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %485 = "llvm.and"(%484, %50) : (i64, i64) -> i64
    %486 = "llvm.or"(%483, %485) : (i64, i64) -> i64
    %487 = "llvm.shl"(%451, %17) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %488 = "llvm.or"(%486, %487) : (i64, i64) -> i64
    %489 = "llvm.getelementptr"(%arg0, %2) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%488, %489) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

set_option maxRecDepth 100000 in
def fd_curve25519_scalar_reduce : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_curve25519_scalar_reduce_region with
    @fd_ulong_load_8 := fd_ulong_load_8]

end Firedancer.Common

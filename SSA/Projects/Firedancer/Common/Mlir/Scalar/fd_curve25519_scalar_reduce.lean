/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/{ref,avx512}/region/fd_curve25519_scalar_reduce.mlir
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Common.Mlir.fd_ulong_load_8

namespace Firedancer.Common
open LeanMLIR SLLVM

-- 498 lines in one block: the quotation's own recursion, not the proof's.
set_option maxRecDepth 100000 in
def fd_curve25519_scalar_reduce_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 2097151 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 21 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 42 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 20 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 41 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 18 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 39 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = 17 : i64}> : () -> i64
    %15 = "llvm.mlir.constant"() <{value = 38 : i64}> : () -> i64
    %16 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %17 = "llvm.mlir.constant"() <{value = 37 : i64}> : () -> i64
    %18 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %19 = "llvm.mlir.constant"() <{value = 15 : i64}> : () -> i64
    %20 = "llvm.mlir.constant"() <{value = 36 : i64}> : () -> i64
    %21 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %22 = "llvm.mlir.constant"() <{value = 14 : i64}> : () -> i64
    %23 = "llvm.mlir.constant"() <{value = 35 : i64}> : () -> i64
    %24 = "llvm.mlir.constant"() <{value = 666643 : i64}> : () -> i64
    %25 = "llvm.mlir.constant"() <{value = 470296 : i64}> : () -> i64
    %26 = "llvm.mlir.constant"() <{value = 654183 : i64}> : () -> i64
    %27 = "llvm.mlir.constant"() <{value = -997805 : i64}> : () -> i64
    %28 = "llvm.mlir.constant"() <{value = 136657 : i64}> : () -> i64
    %29 = "llvm.mlir.constant"() <{value = -683901 : i64}> : () -> i64
    %30 = "llvm.mlir.constant"() <{value = 1048576 : i64}> : () -> i64
    %31 = "llvm.mlir.constant"() <{value = 8796090925056 : i64}> : () -> i64
    %32 = "llvm.mlir.constant"() <{value = -2097152 : i64}> : () -> i64
    %33 = "llvm.mlir.constant"() <{value = 4398044413952 : i64}> : () -> i64
    %34 = "llvm.mlir.constant"() <{value = 9223367638808264704 : i64}> : () -> i64
    %35 = "llvm.mlir.constant"() <{value = 63 : i64}> : () -> i64
    %36 = "llvm.mlir.constant"() <{value = 1048575 : i64}> : () -> i64
    %37 = "llvm.mlir.constant"() <{value = 2199022206976 : i64}> : () -> i64
    %38 = "llvm.mlir.constant"() <{value = 4611683819404132352 : i64}> : () -> i64
    %39 = "llvm.mlir.constant"() <{value = 62 : i64}> : () -> i64
    %40 = "llvm.mlir.constant"() <{value = 524287 : i64}> : () -> i64
    %41 = "llvm.mlir.constant"() <{value = 1099511103488 : i64}> : () -> i64
    %42 = "llvm.mlir.constant"() <{value = 2305841909702066176 : i64}> : () -> i64
    %43 = "llvm.mlir.constant"() <{value = 61 : i64}> : () -> i64
    %44 = "llvm.mlir.constant"() <{value = 262143 : i64}> : () -> i64
    %45 = "llvm.mlir.constant"() <{value = 549755551744 : i64}> : () -> i64
    %46 = "llvm.call"(%arg1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_load_8, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i64
    %47 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 8>}> : (!llvm.ptr) -> !llvm.ptr
    %48 = "llvm.call"(%47) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_load_8, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i64
    %49 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
    %50 = "llvm.call"(%49) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_load_8, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i64
    %51 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 24>}> : (!llvm.ptr) -> !llvm.ptr
    %52 = "llvm.call"(%51) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_load_8, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i64
    %53 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 32>}> : (!llvm.ptr) -> !llvm.ptr
    %54 = "llvm.call"(%53) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_load_8, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i64
    %55 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 40>}> : (!llvm.ptr) -> !llvm.ptr
    %56 = "llvm.call"(%55) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_load_8, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i64
    %57 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 48>}> : (!llvm.ptr) -> !llvm.ptr
    %58 = "llvm.call"(%57) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_load_8, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i64
    %59 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 56>}> : (!llvm.ptr) -> !llvm.ptr
    %60 = "llvm.call"(%59) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_load_8, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i64
    %61 = "llvm.and"(%46, %2) : (i64, i64) -> i64
    %62 = "llvm.lshr"(%46, %3) : (i64, i64) -> i64
    %63 = "llvm.and"(%62, %2) : (i64, i64) -> i64
    %64 = "llvm.lshr"(%46, %4) : (i64, i64) -> i64
    %65 = "llvm.and"(%64, %2) : (i64, i64) -> i64
    %66 = "llvm.intr.fshl"(%48, %46, %5) : (i64, i64, i64) -> i64
    %67 = "llvm.and"(%66, %2) : (i64, i64) -> i64
    %68 = "llvm.lshr"(%48, %6) : (i64, i64) -> i64
    %69 = "llvm.and"(%68, %2) : (i64, i64) -> i64
    %70 = "llvm.lshr"(%48, %7) : (i64, i64) -> i64
    %71 = "llvm.and"(%70, %2) : (i64, i64) -> i64
    %72 = "llvm.intr.fshl"(%50, %48, %8) : (i64, i64, i64) -> i64
    %73 = "llvm.and"(%72, %2) : (i64, i64) -> i64
    %74 = "llvm.lshr"(%50, %9) : (i64, i64) -> i64
    %75 = "llvm.and"(%74, %2) : (i64, i64) -> i64
    %76 = "llvm.lshr"(%50, %1) : (i64, i64) -> i64
    %77 = "llvm.and"(%76, %2) : (i64, i64) -> i64
    %78 = "llvm.intr.fshl"(%52, %50, %10) : (i64, i64, i64) -> i64
    %79 = "llvm.and"(%78, %2) : (i64, i64) -> i64
    %80 = "llvm.lshr"(%52, %11) : (i64, i64) -> i64
    %81 = "llvm.and"(%80, %2) : (i64, i64) -> i64
    %82 = "llvm.lshr"(%52, %12) : (i64, i64) -> i64
    %83 = "llvm.and"(%82, %2) : (i64, i64) -> i64
    %84 = "llvm.intr.fshl"(%54, %52, %13) : (i64, i64, i64) -> i64
    %85 = "llvm.and"(%84, %2) : (i64, i64) -> i64
    %86 = "llvm.lshr"(%54, %14) : (i64, i64) -> i64
    %87 = "llvm.and"(%86, %2) : (i64, i64) -> i64
    %88 = "llvm.lshr"(%54, %15) : (i64, i64) -> i64
    %89 = "llvm.and"(%88, %2) : (i64, i64) -> i64
    %90 = "llvm.intr.fshl"(%56, %54, %16) : (i64, i64, i64) -> i64
    %91 = "llvm.and"(%90, %2) : (i64, i64) -> i64
    %92 = "llvm.lshr"(%56, %0) : (i64, i64) -> i64
    %93 = "llvm.and"(%92, %2) : (i64, i64) -> i64
    %94 = "llvm.lshr"(%56, %17) : (i64, i64) -> i64
    %95 = "llvm.and"(%94, %2) : (i64, i64) -> i64
    %96 = "llvm.intr.fshl"(%58, %56, %18) : (i64, i64, i64) -> i64
    %97 = "llvm.and"(%96, %2) : (i64, i64) -> i64
    %98 = "llvm.lshr"(%58, %19) : (i64, i64) -> i64
    %99 = "llvm.and"(%98, %2) : (i64, i64) -> i64
    %100 = "llvm.lshr"(%58, %20) : (i64, i64) -> i64
    %101 = "llvm.and"(%100, %2) : (i64, i64) -> i64
    %102 = "llvm.intr.fshl"(%60, %58, %21) : (i64, i64, i64) -> i64
    %103 = "llvm.and"(%102, %2) : (i64, i64) -> i64
    %104 = "llvm.lshr"(%60, %22) : (i64, i64) -> i64
    %105 = "llvm.and"(%104, %2) : (i64, i64) -> i64
    %106 = "llvm.lshr"(%60, %23) : (i64, i64) -> i64
    %107 = "llvm.mul"(%106, %24) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %108 = "llvm.add"(%107, %83) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %109 = "llvm.mul"(%106, %25) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %110 = "llvm.add"(%109, %85) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %111 = "llvm.mul"(%106, %26) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %112 = "llvm.add"(%111, %87) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %113 = "llvm.mul"(%106, %27) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %114 = "llvm.add"(%113, %89) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %115 = "llvm.mul"(%106, %28) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %116 = "llvm.add"(%115, %91) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %117 = "llvm.mul"(%106, %29) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %118 = "llvm.add"(%117, %93) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %119 = "llvm.mul"(%105, %24) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %120 = "llvm.mul"(%105, %25) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %121 = "llvm.mul"(%105, %26) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %122 = "llvm.mul"(%105, %27) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %123 = "llvm.mul"(%105, %28) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %124 = "llvm.add"(%114, %123) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %125 = "llvm.mul"(%105, %29) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %126 = "llvm.add"(%116, %125) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %127 = "llvm.mul"(%103, %24) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %128 = "llvm.mul"(%103, %25) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %129 = "llvm.mul"(%103, %26) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %130 = "llvm.mul"(%103, %27) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %131 = "llvm.mul"(%103, %28) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %132 = "llvm.mul"(%103, %29) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %133 = "llvm.add"(%124, %132) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %134 = "llvm.mul"(%101, %24) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %135 = "llvm.add"(%134, %77) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %136 = "llvm.mul"(%101, %25) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %137 = "llvm.mul"(%101, %26) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %138 = "llvm.mul"(%101, %27) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %139 = "llvm.mul"(%101, %28) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %140 = "llvm.mul"(%101, %29) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %141 = "llvm.mul"(%99, %24) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %142 = "llvm.add"(%141, %75) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %143 = "llvm.mul"(%99, %25) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %144 = "llvm.add"(%135, %143) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %145 = "llvm.mul"(%99, %26) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %146 = "llvm.mul"(%99, %27) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %147 = "llvm.mul"(%99, %28) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %148 = "llvm.mul"(%99, %29) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %149 = "llvm.add"(%110, %139) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %150 = "llvm.add"(%149, %148) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %151 = "llvm.add"(%150, %121) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %152 = "llvm.add"(%151, %130) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %153 = "llvm.mul"(%97, %24) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %154 = "llvm.add"(%153, %73) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %155 = "llvm.mul"(%97, %25) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %156 = "llvm.add"(%142, %155) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %157 = "llvm.mul"(%97, %26) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %158 = "llvm.add"(%144, %157) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %159 = "llvm.mul"(%97, %27) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %160 = "llvm.mul"(%97, %28) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %161 = "llvm.add"(%137, %81) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %162 = "llvm.add"(%161, %146) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %163 = "llvm.add"(%162, %160) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %164 = "llvm.add"(%163, %119) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %165 = "llvm.add"(%164, %128) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %166 = "llvm.mul"(%97, %29) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %167 = "llvm.add"(%154, %30) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %168 = "llvm.lshr"(%167, %3) : (i64, i64) -> i64
    %169 = "llvm.add"(%156, %168) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %170 = "llvm.and"(%167, %31) : (i64, i64) -> i64
    %171 = "llvm.sub"(%154, %170) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %172 = "llvm.add"(%158, %30) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %173 = "llvm.lshr"(%172, %3) : (i64, i64) -> i64
    %174 = "llvm.add"(%136, %79) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %175 = "llvm.add"(%174, %145) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %176 = "llvm.add"(%175, %159) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %177 = "llvm.add"(%176, %127) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %178 = "llvm.add"(%177, %173) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %179 = "llvm.and"(%172, %32) : (i64, i64) -> i64
    %180 = "llvm.sub"(%158, %179) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %181 = "llvm.add"(%165, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %182 = "llvm.ashr"(%181, %3) : (i64, i64) -> i64
    %183 = "llvm.add"(%108, %138) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %184 = "llvm.add"(%183, %147) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %185 = "llvm.add"(%184, %166) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %186 = "llvm.add"(%185, %120) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %187 = "llvm.add"(%186, %129) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %188 = "llvm.add"(%187, %182) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %189 = "llvm.and"(%181, %32) : (i64, i64) -> i64
    %190 = "llvm.add"(%152, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %191 = "llvm.ashr"(%190, %3) : (i64, i64) -> i64
    %192 = "llvm.add"(%112, %140) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %193 = "llvm.add"(%192, %122) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %194 = "llvm.add"(%193, %131) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %195 = "llvm.add"(%194, %191) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %196 = "llvm.and"(%190, %32) : (i64, i64) -> i64
    %197 = "llvm.sub"(%152, %196) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %198 = "llvm.add"(%133, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %199 = "llvm.ashr"(%198, %3) : (i64, i64) -> i64
    %200 = "llvm.add"(%126, %199) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %201 = "llvm.and"(%198, %32) : (i64, i64) -> i64
    %202 = "llvm.sub"(%133, %201) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %203 = "llvm.add"(%118, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %204 = "llvm.ashr"(%203, %3) : (i64, i64) -> i64
    %205 = "llvm.add"(%204, %95) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %206 = "llvm.and"(%203, %32) : (i64, i64) -> i64
    %207 = "llvm.sub"(%118, %206) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %208 = "llvm.add"(%169, %30) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %209 = "llvm.lshr"(%208, %3) : (i64, i64) -> i64
    %210 = "llvm.and"(%208, %32) : (i64, i64) -> i64
    %211 = "llvm.add"(%178, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %212 = "llvm.ashr"(%211, %3) : (i64, i64) -> i64
    %213 = "llvm.and"(%211, %32) : (i64, i64) -> i64
    %214 = "llvm.add"(%188, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %215 = "llvm.ashr"(%214, %3) : (i64, i64) -> i64
    %216 = "llvm.add"(%215, %197) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %217 = "llvm.and"(%214, %32) : (i64, i64) -> i64
    %218 = "llvm.sub"(%188, %217) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %219 = "llvm.add"(%195, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %220 = "llvm.ashr"(%219, %3) : (i64, i64) -> i64
    %221 = "llvm.add"(%220, %202) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %222 = "llvm.and"(%219, %32) : (i64, i64) -> i64
    %223 = "llvm.sub"(%195, %222) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %224 = "llvm.add"(%200, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %225 = "llvm.ashr"(%224, %3) : (i64, i64) -> i64
    %226 = "llvm.add"(%225, %207) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %227 = "llvm.and"(%224, %32) : (i64, i64) -> i64
    %228 = "llvm.sub"(%200, %227) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %229 = "llvm.mul"(%205, %24) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %230 = "llvm.add"(%229, %71) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %231 = "llvm.mul"(%205, %25) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %232 = "llvm.add"(%171, %231) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %233 = "llvm.mul"(%205, %26) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %234 = "llvm.mul"(%205, %27) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %235 = "llvm.mul"(%205, %28) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %236 = "llvm.mul"(%205, %29) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %237 = "llvm.add"(%165, %236) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %238 = "llvm.sub"(%237, %189) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %239 = "llvm.add"(%238, %212) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %240 = "llvm.mul"(%226, %24) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %241 = "llvm.add"(%240, %69) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %242 = "llvm.mul"(%226, %25) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %243 = "llvm.add"(%230, %242) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %244 = "llvm.mul"(%226, %26) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %245 = "llvm.add"(%232, %244) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %246 = "llvm.mul"(%226, %27) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %247 = "llvm.mul"(%226, %28) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %248 = "llvm.mul"(%226, %29) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %249 = "llvm.mul"(%228, %24) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %250 = "llvm.add"(%249, %67) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %251 = "llvm.mul"(%228, %25) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %252 = "llvm.add"(%241, %251) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %253 = "llvm.mul"(%228, %26) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %254 = "llvm.add"(%243, %253) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %255 = "llvm.mul"(%228, %27) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %256 = "llvm.add"(%245, %255) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %257 = "llvm.mul"(%228, %28) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %258 = "llvm.mul"(%228, %29) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %259 = "llvm.add"(%180, %234) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %260 = "llvm.add"(%259, %209) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %261 = "llvm.add"(%260, %247) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %262 = "llvm.add"(%261, %258) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %263 = "llvm.mul"(%221, %24) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %264 = "llvm.add"(%263, %65) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %265 = "llvm.mul"(%221, %25) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %266 = "llvm.add"(%250, %265) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %267 = "llvm.mul"(%221, %26) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %268 = "llvm.add"(%252, %267) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %269 = "llvm.mul"(%221, %27) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %270 = "llvm.add"(%254, %269) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %271 = "llvm.mul"(%221, %28) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %272 = "llvm.add"(%256, %271) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %273 = "llvm.mul"(%221, %29) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %274 = "llvm.mul"(%223, %24) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %275 = "llvm.add"(%274, %63) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %276 = "llvm.mul"(%223, %25) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %277 = "llvm.add"(%264, %276) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %278 = "llvm.mul"(%223, %26) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %279 = "llvm.add"(%266, %278) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %280 = "llvm.mul"(%223, %27) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %281 = "llvm.add"(%268, %280) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %282 = "llvm.mul"(%223, %28) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %283 = "llvm.add"(%270, %282) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %284 = "llvm.mul"(%223, %29) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %285 = "llvm.add"(%272, %284) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %286 = "llvm.mul"(%216, %24) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %287 = "llvm.add"(%286, %61) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %288 = "llvm.mul"(%216, %25) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %289 = "llvm.add"(%275, %288) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %290 = "llvm.mul"(%216, %26) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %291 = "llvm.add"(%277, %290) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %292 = "llvm.mul"(%216, %27) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %293 = "llvm.add"(%279, %292) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %294 = "llvm.mul"(%216, %28) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %295 = "llvm.add"(%281, %294) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %296 = "llvm.mul"(%216, %29) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %297 = "llvm.add"(%283, %296) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %298 = "llvm.add"(%287, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %299 = "llvm.ashr"(%298, %3) : (i64, i64) -> i64
    %300 = "llvm.add"(%289, %299) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %301 = "llvm.and"(%298, %32) : (i64, i64) -> i64
    %302 = "llvm.sub"(%287, %301) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %303 = "llvm.add"(%291, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %304 = "llvm.ashr"(%303, %3) : (i64, i64) -> i64
    %305 = "llvm.add"(%293, %304) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %306 = "llvm.and"(%303, %32) : (i64, i64) -> i64
    %307 = "llvm.sub"(%291, %306) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %308 = "llvm.add"(%295, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %309 = "llvm.ashr"(%308, %3) : (i64, i64) -> i64
    %310 = "llvm.add"(%297, %309) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %311 = "llvm.and"(%308, %32) : (i64, i64) -> i64
    %312 = "llvm.sub"(%295, %311) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %313 = "llvm.add"(%285, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %314 = "llvm.ashr"(%313, %3) : (i64, i64) -> i64
    %315 = "llvm.add"(%233, %169) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %316 = "llvm.sub"(%315, %210) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %317 = "llvm.add"(%316, %246) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %318 = "llvm.add"(%317, %257) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %319 = "llvm.add"(%318, %273) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %320 = "llvm.add"(%319, %314) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %321 = "llvm.and"(%313, %32) : (i64, i64) -> i64
    %322 = "llvm.sub"(%285, %321) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %323 = "llvm.add"(%262, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %324 = "llvm.ashr"(%323, %3) : (i64, i64) -> i64
    %325 = "llvm.add"(%178, %235) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %326 = "llvm.sub"(%325, %213) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %327 = "llvm.add"(%326, %248) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %328 = "llvm.add"(%327, %324) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %329 = "llvm.and"(%323, %32) : (i64, i64) -> i64
    %330 = "llvm.sub"(%262, %329) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %331 = "llvm.add"(%239, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %332 = "llvm.ashr"(%331, %3) : (i64, i64) -> i64
    %333 = "llvm.add"(%332, %218) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %334 = "llvm.and"(%331, %32) : (i64, i64) -> i64
    %335 = "llvm.sub"(%239, %334) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %336 = "llvm.add"(%300, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %337 = "llvm.ashr"(%336, %3) : (i64, i64) -> i64
    %338 = "llvm.and"(%336, %32) : (i64, i64) -> i64
    %339 = "llvm.add"(%305, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %340 = "llvm.ashr"(%339, %3) : (i64, i64) -> i64
    %341 = "llvm.and"(%339, %32) : (i64, i64) -> i64
    %342 = "llvm.add"(%310, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %343 = "llvm.ashr"(%342, %3) : (i64, i64) -> i64
    %344 = "llvm.add"(%322, %343) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %345 = "llvm.and"(%342, %32) : (i64, i64) -> i64
    %346 = "llvm.add"(%320, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %347 = "llvm.ashr"(%346, %3) : (i64, i64) -> i64
    %348 = "llvm.add"(%330, %347) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %349 = "llvm.and"(%346, %32) : (i64, i64) -> i64
    %350 = "llvm.sub"(%320, %349) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %351 = "llvm.add"(%328, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %352 = "llvm.ashr"(%351, %3) : (i64, i64) -> i64
    %353 = "llvm.add"(%335, %352) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %354 = "llvm.and"(%351, %32) : (i64, i64) -> i64
    %355 = "llvm.sub"(%328, %354) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %356 = "llvm.add"(%333, %30) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %357 = "llvm.ashr"(%356, %3) : (i64, i64) -> i64
    %358 = "llvm.and"(%356, %32) : (i64, i64) -> i64
    %359 = "llvm.sub"(%333, %358) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %360 = "llvm.mul"(%357, %24) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %361 = "llvm.add"(%302, %360) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %362 = "llvm.mul"(%357, %25) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %363 = "llvm.mul"(%357, %26) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %364 = "llvm.mul"(%357, %27) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %365 = "llvm.mul"(%357, %28) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %366 = "llvm.mul"(%357, %29) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %367 = "llvm.ashr"(%361, %3) : (i64, i64) -> i64
    %368 = "llvm.add"(%362, %300) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %369 = "llvm.sub"(%368, %338) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %370 = "llvm.add"(%369, %367) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %371 = "llvm.and"(%361, %2) : (i64, i64) -> i64
    %372 = "llvm.ashr"(%370, %3) : (i64, i64) -> i64
    %373 = "llvm.add"(%307, %363) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %374 = "llvm.add"(%373, %337) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %375 = "llvm.add"(%374, %372) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %376 = "llvm.and"(%370, %2) : (i64, i64) -> i64
    %377 = "llvm.ashr"(%375, %3) : (i64, i64) -> i64
    %378 = "llvm.add"(%305, %364) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %379 = "llvm.sub"(%378, %341) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %380 = "llvm.add"(%379, %377) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %381 = "llvm.and"(%375, %2) : (i64, i64) -> i64
    %382 = "llvm.ashr"(%380, %3) : (i64, i64) -> i64
    %383 = "llvm.add"(%312, %365) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %384 = "llvm.add"(%383, %340) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %385 = "llvm.add"(%384, %382) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %386 = "llvm.and"(%380, %2) : (i64, i64) -> i64
    %387 = "llvm.ashr"(%385, %3) : (i64, i64) -> i64
    %388 = "llvm.add"(%310, %366) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %389 = "llvm.sub"(%388, %345) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %390 = "llvm.add"(%389, %387) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %391 = "llvm.and"(%385, %2) : (i64, i64) -> i64
    %392 = "llvm.ashr"(%390, %3) : (i64, i64) -> i64
    %393 = "llvm.add"(%344, %392) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %394 = "llvm.and"(%390, %2) : (i64, i64) -> i64
    %395 = "llvm.ashr"(%393, %3) : (i64, i64) -> i64
    %396 = "llvm.add"(%395, %350) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %397 = "llvm.and"(%393, %2) : (i64, i64) -> i64
    %398 = "llvm.ashr"(%396, %3) : (i64, i64) -> i64
    %399 = "llvm.add"(%348, %398) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %400 = "llvm.and"(%396, %2) : (i64, i64) -> i64
    %401 = "llvm.ashr"(%399, %3) : (i64, i64) -> i64
    %402 = "llvm.add"(%401, %355) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %403 = "llvm.and"(%399, %2) : (i64, i64) -> i64
    %404 = "llvm.ashr"(%402, %3) : (i64, i64) -> i64
    %405 = "llvm.add"(%353, %404) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %406 = "llvm.and"(%402, %2) : (i64, i64) -> i64
    %407 = "llvm.ashr"(%405, %3) : (i64, i64) -> i64
    %408 = "llvm.add"(%407, %359) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %409 = "llvm.and"(%405, %2) : (i64, i64) -> i64
    %410 = "llvm.ashr"(%408, %3) : (i64, i64) -> i64
    %411 = "llvm.and"(%408, %2) : (i64, i64) -> i64
    %412 = "llvm.mul"(%410, %24) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %413 = "llvm.add"(%412, %371) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %414 = "llvm.mul"(%410, %25) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %415 = "llvm.add"(%414, %376) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %416 = "llvm.mul"(%410, %26) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %417 = "llvm.add"(%416, %381) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %418 = "llvm.mul"(%410, %27) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %419 = "llvm.add"(%418, %386) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %420 = "llvm.mul"(%410, %28) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %421 = "llvm.add"(%420, %391) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %422 = "llvm.mul"(%410, %29) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %423 = "llvm.add"(%422, %394) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %424 = "llvm.ashr"(%413, %3) : (i64, i64) -> i64
    %425 = "llvm.add"(%415, %424) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %426 = "llvm.and"(%413, %2) : (i64, i64) -> i64
    %427 = "llvm.ashr"(%425, %3) : (i64, i64) -> i64
    %428 = "llvm.add"(%417, %427) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %429 = "llvm.ashr"(%428, %3) : (i64, i64) -> i64
    %430 = "llvm.add"(%419, %429) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %431 = "llvm.ashr"(%430, %3) : (i64, i64) -> i64
    %432 = "llvm.add"(%421, %431) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %433 = "llvm.ashr"(%432, %3) : (i64, i64) -> i64
    %434 = "llvm.add"(%423, %433) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %435 = "llvm.ashr"(%434, %3) : (i64, i64) -> i64
    %436 = "llvm.add"(%435, %397) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %437 = "llvm.ashr"(%436, %3) : (i64, i64) -> i64
    %438 = "llvm.add"(%437, %400) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %439 = "llvm.ashr"(%438, %3) : (i64, i64) -> i64
    %440 = "llvm.add"(%439, %403) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %441 = "llvm.ashr"(%440, %3) : (i64, i64) -> i64
    %442 = "llvm.add"(%441, %406) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %443 = "llvm.ashr"(%442, %3) : (i64, i64) -> i64
    %444 = "llvm.add"(%443, %409) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %445 = "llvm.ashr"(%444, %3) : (i64, i64) -> i64
    %446 = "llvm.add"(%445, %411) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %447 = "llvm.shl"(%425, %3) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %448 = "llvm.and"(%447, %33) : (i64, i64) -> i64
    %449 = "llvm.or"(%448, %426) : (i64, i64) -> i64
    %450 = "llvm.shl"(%428, %4) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %451 = "llvm.and"(%450, %34) : (i64, i64) -> i64
    %452 = "llvm.or"(%449, %451) : (i64, i64) -> i64
    %453 = "llvm.shl"(%430, %35) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %454 = "llvm.or"(%452, %453) : (i64, i64) -> i64
    "llvm.store"(%454, %arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %455 = "llvm.lshr"(%430, %5) : (i64, i64) -> i64
    %456 = "llvm.and"(%455, %36) : (i64, i64) -> i64
    %457 = "llvm.shl"(%432, %6) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %458 = "llvm.and"(%457, %37) : (i64, i64) -> i64
    %459 = "llvm.or"(%458, %456) : (i64, i64) -> i64
    %460 = "llvm.shl"(%434, %7) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %461 = "llvm.and"(%460, %38) : (i64, i64) -> i64
    %462 = "llvm.or"(%459, %461) : (i64, i64) -> i64
    %463 = "llvm.shl"(%436, %39) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %464 = "llvm.or"(%462, %463) : (i64, i64) -> i64
    %465 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 8>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%464, %465) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %466 = "llvm.lshr"(%436, %8) : (i64, i64) -> i64
    %467 = "llvm.and"(%466, %40) : (i64, i64) -> i64
    %468 = "llvm.shl"(%438, %9) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %469 = "llvm.and"(%468, %41) : (i64, i64) -> i64
    %470 = "llvm.or"(%469, %467) : (i64, i64) -> i64
    %471 = "llvm.shl"(%440, %1) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %472 = "llvm.and"(%471, %42) : (i64, i64) -> i64
    %473 = "llvm.or"(%470, %472) : (i64, i64) -> i64
    %474 = "llvm.shl"(%442, %43) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %475 = "llvm.or"(%473, %474) : (i64, i64) -> i64
    %476 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%475, %476) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %477 = "llvm.lshr"(%442, %10) : (i64, i64) -> i64
    %478 = "llvm.and"(%477, %44) : (i64, i64) -> i64
    %479 = "llvm.shl"(%444, %11) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %480 = "llvm.and"(%479, %45) : (i64, i64) -> i64
    %481 = "llvm.or"(%478, %480) : (i64, i64) -> i64
    %482 = "llvm.shl"(%446, %12) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %483 = "llvm.or"(%481, %482) : (i64, i64) -> i64
    %484 = "llvm.getelementptr"(%arg0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 24>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%483, %484) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

set_option maxRecDepth 100000 in
sllvm_cfg_def fd_curve25519_scalar_reduce : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_curve25519_scalar_reduce_region with
    @fd_ulong_load_8 := fd_ulong_load_8]

end Firedancer.Common

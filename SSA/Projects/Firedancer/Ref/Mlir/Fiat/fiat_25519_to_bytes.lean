/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_addcarryx_u51
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_subborrowx_u51
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_cmovznz_u64

/-!
# `fiat_25519_to_bytes` (ref)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/ref/region/fiat_25519_to_bytes.mlir`. Fully reduces the
five limbs mod `p` -- a borrow chain against `p`, a `cmovznz` mask, then an
add-back -- and serialises the result little-endian into 32 bytes.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM

set_option maxRecDepth 20000 in
def fiat_25519_to_bytes_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %2 = "llvm.mlir.constant"() <{value = 2251799813685229 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %15 = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
    %16 = "llvm.mlir.constant"() <{value = 48 : i64}> : () -> i64
    %17 = "llvm.mlir.constant"() <{value = 255 : i64}> : () -> i64
    %18 = "llvm.mlir.constant"() <{value = 56 : i64}> : () -> i64
    %19 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %20 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %21 = "llvm.mlir.constant"() <{value = 9 : i64}> : () -> i64
    %22 = "llvm.mlir.constant"() <{value = 10 : i64}> : () -> i64
    %23 = "llvm.mlir.constant"() <{value = 11 : i64}> : () -> i64
    %24 = "llvm.mlir.constant"() <{value = 12 : i64}> : () -> i64
    %25 = "llvm.mlir.constant"() <{value = 13 : i64}> : () -> i64
    %26 = "llvm.mlir.constant"() <{value = 14 : i64}> : () -> i64
    %27 = "llvm.mlir.constant"() <{value = 15 : i64}> : () -> i64
    %28 = "llvm.mlir.constant"() <{value = 17 : i64}> : () -> i64
    %29 = "llvm.mlir.constant"() <{value = 18 : i64}> : () -> i64
    %30 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %31 = "llvm.mlir.constant"() <{value = 20 : i64}> : () -> i64
    %32 = "llvm.mlir.constant"() <{value = 21 : i64}> : () -> i64
    %33 = "llvm.mlir.constant"() <{value = 22 : i64}> : () -> i64
    %34 = "llvm.mlir.constant"() <{value = 23 : i64}> : () -> i64
    %35 = "llvm.mlir.constant"() <{value = 25 : i64}> : () -> i64
    %36 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %37 = "llvm.mlir.constant"() <{value = 27 : i64}> : () -> i64
    %38 = "llvm.mlir.constant"() <{value = 28 : i64}> : () -> i64
    %39 = "llvm.mlir.constant"() <{value = 29 : i64}> : () -> i64
    %40 = "llvm.mlir.constant"() <{value = 30 : i64}> : () -> i64
    %41 = "llvm.mlir.constant"() <{value = 31 : i64}> : () -> i64
    %42 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %43 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %44 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %45 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %46 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %47 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %48 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %49 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %50 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %51 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %52 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %53 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %54 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %55 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %56 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %57 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %58 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %59 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %60 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %61 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %62 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%42) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%43) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%44) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%45) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%46) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%47) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%48) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%49) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%50) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%51) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%52) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%53) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%54) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%55) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%56) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%57) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%58) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%59) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%60) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%61) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%62) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    %63 = "llvm.load"(%arg1) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%42, %43, %1, %63, %2) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_subborrowx_u51, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i8, i64, i64) -> ()
    %64 = "llvm.load"(%43) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %65 = "llvm.getelementptr"(%arg1, %3) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %66 = "llvm.load"(%65) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%44, %45, %64, %66, %4) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_subborrowx_u51, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i8, i64, i64) -> ()
    %67 = "llvm.load"(%45) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %68 = "llvm.getelementptr"(%arg1, %5) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %69 = "llvm.load"(%68) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%46, %47, %67, %69, %4) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_subborrowx_u51, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i8, i64, i64) -> ()
    %70 = "llvm.load"(%47) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %71 = "llvm.getelementptr"(%arg1, %6) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %72 = "llvm.load"(%71) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%48, %49, %70, %72, %4) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_subborrowx_u51, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i8, i64, i64) -> ()
    %73 = "llvm.load"(%49) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %74 = "llvm.getelementptr"(%arg1, %7) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %75 = "llvm.load"(%74) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%50, %51, %73, %75, %4) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_subborrowx_u51, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i8, i64, i64) -> ()
    %76 = "llvm.load"(%51) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    "llvm.call"(%52, %76, %8, %9) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_cmovznz_u64, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, i8, i64, i64) -> ()
    %77 = "llvm.load"(%42) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %78 = "llvm.load"(%52) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %79 = "llvm.and"(%78, %2) : (i64, i64) -> i64
    "llvm.call"(%53, %54, %1, %77, %79) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_addcarryx_u51, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i8, i64, i64) -> ()
    %80 = "llvm.load"(%54) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %81 = "llvm.load"(%44) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %82 = "llvm.and"(%78, %4) : (i64, i64) -> i64
    "llvm.call"(%55, %56, %80, %81, %82) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_addcarryx_u51, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i8, i64, i64) -> ()
    %83 = "llvm.load"(%56) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %84 = "llvm.load"(%46) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%57, %58, %83, %84, %82) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_addcarryx_u51, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i8, i64, i64) -> ()
    %85 = "llvm.load"(%58) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %86 = "llvm.load"(%48) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%59, %60, %85, %86, %82) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_addcarryx_u51, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i8, i64, i64) -> ()
    %87 = "llvm.load"(%60) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %88 = "llvm.load"(%50) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%61, %62, %87, %88, %82) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_addcarryx_u51, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i8, i64, i64) -> ()
    %89 = "llvm.load"(%61) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %90 = "llvm.shl"(%89, %7) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %91 = "llvm.load"(%59) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %92 = "llvm.shl"(%91, %3) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %93 = "llvm.load"(%57) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %94 = "llvm.shl"(%93, %10) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %95 = "llvm.load"(%55) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %96 = "llvm.shl"(%95, %6) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %97 = "llvm.load"(%53) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %98 = "llvm.trunc"(%97) : (i64) -> i8
    %99 = "llvm.lshr"(%97, %11) : (i64, i64) -> i64
    %100 = "llvm.trunc"(%99) : (i64) -> i8
    %101 = "llvm.lshr"(%97, %12) : (i64, i64) -> i64
    %102 = "llvm.trunc"(%101) : (i64) -> i8
    %103 = "llvm.lshr"(%97, %13) : (i64, i64) -> i64
    %104 = "llvm.trunc"(%103) : (i64) -> i8
    %105 = "llvm.lshr"(%97, %14) : (i64, i64) -> i64
    %106 = "llvm.trunc"(%105) : (i64) -> i8
    %107 = "llvm.lshr"(%97, %15) : (i64, i64) -> i64
    %108 = "llvm.trunc"(%107) : (i64) -> i8
    %109 = "llvm.lshr"(%97, %16) : (i64, i64) -> i64
    %110 = "llvm.and"(%109, %17) : (i64, i64) -> i64
    %111 = "llvm.add"(%110, %96) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %112 = "llvm.trunc"(%111) : (i64) -> i8
    %113 = "llvm.lshr"(%111, %11) : (i64, i64) -> i64
    %114 = "llvm.trunc"(%113) : (i64) -> i8
    %115 = "llvm.lshr"(%111, %12) : (i64, i64) -> i64
    %116 = "llvm.trunc"(%115) : (i64) -> i8
    %117 = "llvm.lshr"(%111, %13) : (i64, i64) -> i64
    %118 = "llvm.trunc"(%117) : (i64) -> i8
    %119 = "llvm.lshr"(%111, %14) : (i64, i64) -> i64
    %120 = "llvm.trunc"(%119) : (i64) -> i8
    %121 = "llvm.lshr"(%111, %15) : (i64, i64) -> i64
    %122 = "llvm.trunc"(%121) : (i64) -> i8
    %123 = "llvm.lshr"(%111, %16) : (i64, i64) -> i64
    %124 = "llvm.and"(%123, %17) : (i64, i64) -> i64
    %125 = "llvm.add"(%124, %94) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %126 = "llvm.trunc"(%125) : (i64) -> i8
    %127 = "llvm.lshr"(%125, %11) : (i64, i64) -> i64
    %128 = "llvm.trunc"(%127) : (i64) -> i8
    %129 = "llvm.lshr"(%125, %12) : (i64, i64) -> i64
    %130 = "llvm.trunc"(%129) : (i64) -> i8
    %131 = "llvm.lshr"(%125, %13) : (i64, i64) -> i64
    %132 = "llvm.trunc"(%131) : (i64) -> i8
    %133 = "llvm.lshr"(%125, %14) : (i64, i64) -> i64
    %134 = "llvm.trunc"(%133) : (i64) -> i8
    %135 = "llvm.lshr"(%125, %15) : (i64, i64) -> i64
    %136 = "llvm.trunc"(%135) : (i64) -> i8
    %137 = "llvm.lshr"(%125, %16) : (i64, i64) -> i64
    %138 = "llvm.trunc"(%137) : (i64) -> i8
    %139 = "llvm.lshr"(%125, %18) : (i64, i64) -> i64
    %140 = "llvm.add"(%139, %92) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %141 = "llvm.trunc"(%140) : (i64) -> i8
    %142 = "llvm.lshr"(%140, %11) : (i64, i64) -> i64
    %143 = "llvm.trunc"(%142) : (i64) -> i8
    %144 = "llvm.lshr"(%140, %12) : (i64, i64) -> i64
    %145 = "llvm.trunc"(%144) : (i64) -> i8
    %146 = "llvm.lshr"(%140, %13) : (i64, i64) -> i64
    %147 = "llvm.trunc"(%146) : (i64) -> i8
    %148 = "llvm.lshr"(%140, %14) : (i64, i64) -> i64
    %149 = "llvm.trunc"(%148) : (i64) -> i8
    %150 = "llvm.lshr"(%140, %15) : (i64, i64) -> i64
    %151 = "llvm.trunc"(%150) : (i64) -> i8
    %152 = "llvm.lshr"(%140, %16) : (i64, i64) -> i64
    %153 = "llvm.and"(%152, %17) : (i64, i64) -> i64
    %154 = "llvm.add"(%153, %90) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %155 = "llvm.trunc"(%154) : (i64) -> i8
    %156 = "llvm.lshr"(%154, %11) : (i64, i64) -> i64
    %157 = "llvm.trunc"(%156) : (i64) -> i8
    %158 = "llvm.lshr"(%154, %12) : (i64, i64) -> i64
    %159 = "llvm.trunc"(%158) : (i64) -> i8
    %160 = "llvm.lshr"(%154, %13) : (i64, i64) -> i64
    %161 = "llvm.trunc"(%160) : (i64) -> i8
    %162 = "llvm.lshr"(%154, %14) : (i64, i64) -> i64
    %163 = "llvm.trunc"(%162) : (i64) -> i8
    %164 = "llvm.lshr"(%154, %15) : (i64, i64) -> i64
    %165 = "llvm.trunc"(%164) : (i64) -> i8
    %166 = "llvm.lshr"(%154, %16) : (i64, i64) -> i64
    %167 = "llvm.trunc"(%166) : (i64) -> i8
    "llvm.store"(%98, %arg0) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %168 = "llvm.getelementptr"(%arg0, %3) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%100, %168) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %169 = "llvm.getelementptr"(%arg0, %5) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%102, %169) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %170 = "llvm.getelementptr"(%arg0, %6) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%104, %170) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %171 = "llvm.getelementptr"(%arg0, %7) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%106, %171) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %172 = "llvm.getelementptr"(%arg0, %19) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%108, %172) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %173 = "llvm.getelementptr"(%arg0, %10) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%112, %173) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %174 = "llvm.getelementptr"(%arg0, %20) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%114, %174) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %175 = "llvm.getelementptr"(%arg0, %11) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%116, %175) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %176 = "llvm.getelementptr"(%arg0, %21) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%118, %176) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %177 = "llvm.getelementptr"(%arg0, %22) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%120, %177) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %178 = "llvm.getelementptr"(%arg0, %23) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%122, %178) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %179 = "llvm.getelementptr"(%arg0, %24) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%126, %179) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %180 = "llvm.getelementptr"(%arg0, %25) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%128, %180) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %181 = "llvm.getelementptr"(%arg0, %26) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%130, %181) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %182 = "llvm.getelementptr"(%arg0, %27) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%132, %182) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %183 = "llvm.getelementptr"(%arg0, %12) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%134, %183) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %184 = "llvm.getelementptr"(%arg0, %28) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%136, %184) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %185 = "llvm.getelementptr"(%arg0, %29) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%138, %185) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %186 = "llvm.getelementptr"(%arg0, %30) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%141, %186) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %187 = "llvm.getelementptr"(%arg0, %31) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%143, %187) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %188 = "llvm.getelementptr"(%arg0, %32) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%145, %188) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %189 = "llvm.getelementptr"(%arg0, %33) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%147, %189) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %190 = "llvm.getelementptr"(%arg0, %34) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%149, %190) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %191 = "llvm.getelementptr"(%arg0, %13) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%151, %191) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %192 = "llvm.getelementptr"(%arg0, %35) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%155, %192) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %193 = "llvm.getelementptr"(%arg0, %36) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%157, %193) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %194 = "llvm.getelementptr"(%arg0, %37) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%159, %194) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %195 = "llvm.getelementptr"(%arg0, %38) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%161, %195) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %196 = "llvm.getelementptr"(%arg0, %39) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%163, %196) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %197 = "llvm.getelementptr"(%arg0, %40) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%165, %197) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %198 = "llvm.getelementptr"(%arg0, %41) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%167, %198) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%62) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%61) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%60) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%59) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%58) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%57) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%56) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%55) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%54) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%53) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%52) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%51) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%50) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%49) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%48) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%47) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%46) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%45) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%44) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%43) <{size = 1 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%42) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

set_option maxRecDepth 20000 in
def fiat_25519_to_bytes : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [] :=
  [sllvm_cfg_of| fiat_25519_to_bytes_region with
    @fiat_25519_addcarryx_u51 := fiat_25519_addcarryx_u51,
    @fiat_25519_subborrowx_u51 := fiat_25519_subborrowx_u51,
    @fiat_25519_cmovznz_u64 := fiat_25519_cmovznz_u64]

end Firedancer.Ref

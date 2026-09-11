/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/{ref,avx512}/region/fd_sha512_core_ref.mlir
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_ulong_bswap
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_ulong_rotate_right

namespace Firedancer.Common
open LeanMLIR SLLVM

set_option maxRecDepth 100000 in
def fd_sha512_core_ref_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: i64):
    %0 = "llvm.mlir.constant"() <{value = 80 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 9 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 61 : i32}> : () -> i32
    %3 = "llvm.mlir.constant"() <{value = 19 : i32}> : () -> i32
    %4 = "llvm.mlir.constant"() <{value = 8 : i32}> : () -> i32
    %5 = "llvm.mlir.constant"() <{value = 14 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 15 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 39 : i32}> : () -> i32
    %9 = "llvm.mlir.constant"() <{value = 34 : i32}> : () -> i32
    %10 = "llvm.mlir.constant"() <{value = 28 : i32}> : () -> i32
    %11 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %12 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %15 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %16 = "llvm.mlir.constant"() <{value = 14 : i32}> : () -> i32
    %17 = "llvm.mlir.constant"() <{value = 18 : i32}> : () -> i32
    %18 = "llvm.mlir.constant"() <{value = 41 : i32}> : () -> i32
    %19 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %20 = "llvm.mlir.addressof"() <{global_name = @fd_sha512_core_ref.K}> : () -> !llvm.ptr
    %21 = "llvm.alloca"(%11) <{alignment = 16 : i64, elem_type = !llvm.array<16 x i64>}> : (i32) -> !llvm.ptr
    %22 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    %23 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    %24 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    %25 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    %26 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 5>}> : (!llvm.ptr) -> !llvm.ptr
    %27 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 6>}> : (!llvm.ptr) -> !llvm.ptr
    %28 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 7>}> : (!llvm.ptr) -> !llvm.ptr
    %29 = "llvm.load"(%arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %30 = "llvm.load"(%22) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %31 = "llvm.load"(%23) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %32 = "llvm.load"(%24) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %33 = "llvm.load"(%25) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %34 = "llvm.load"(%26) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %35 = "llvm.load"(%27) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %36 = "llvm.load"(%28) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.br"(%36, %35, %34, %33, %32, %31, %30, %29, %arg1, %arg2)[^bb1] : (i64, i64, i64, i64, i64, i64, i64, i64, !llvm.ptr, i64) -> ()
  ^bb1(%37: i64, %38: i64, %39: i64, %40: i64, %41: i64, %42: i64, %43: i64, %44: i64, %45: !llvm.ptr, %46: i64):  // 2 preds: ^bb0, ^bb4
    "llvm.intr.lifetime.start"(%21) <{size = 128 : i64}> : (!llvm.ptr) -> ()
    "llvm.br"(%44, %43, %42, %41, %15, %37, %38, %39, %40)[^bb2] : (i64, i64, i64, i64, i64, i64, i64, i64, i64) -> ()
  ^bb2(%47: i64, %48: i64, %49: i64, %50: i64, %51: i64, %52: i64, %53: i64, %54: i64, %55: i64):  // 2 preds: ^bb1, ^bb2
    %56 = "llvm.getelementptr"(%45, %51) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %57 = "llvm.load"(%56) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %58 = "llvm.call"(%57) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_bswap, fastmathFlags = #llvm.fastmath<none>}> : (i64) -> i64
    %59 = "llvm.getelementptr"(%21, %51) <{elem_type = !llvm.array<16 x i64>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%58, %59) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %60 = "llvm.call"(%55, %16) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %61 = "llvm.call"(%55, %17) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %62 = "llvm.xor"(%61, %60) : (i64, i64) -> i64
    %63 = "llvm.call"(%55, %18) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %64 = "llvm.xor"(%62, %63) : (i64, i64) -> i64
    %65 = "llvm.and"(%54, %55) : (i64, i64) -> i64
    %66 = "llvm.xor"(%55, %19) : (i64, i64) -> i64
    %67 = "llvm.and"(%53, %66) : (i64, i64) -> i64
    %68 = "llvm.getelementptr"(%20, %51) <{elem_type = !llvm.array<80 x i64>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %69 = "llvm.load"(%68) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %70 = "llvm.or"(%67, %65) : (i64, i64) -> i64
    %71 = "llvm.add"(%70, %52) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %72 = "llvm.add"(%71, %58) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %73 = "llvm.add"(%72, %64) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %74 = "llvm.add"(%73, %69) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %75 = "llvm.call"(%47, %10) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %76 = "llvm.call"(%47, %9) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %77 = "llvm.xor"(%76, %75) : (i64, i64) -> i64
    %78 = "llvm.call"(%47, %8) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %79 = "llvm.xor"(%77, %78) : (i64, i64) -> i64
    %80 = "llvm.xor"(%48, %49) : (i64, i64) -> i64
    %81 = "llvm.and"(%47, %80) : (i64, i64) -> i64
    %82 = "llvm.and"(%48, %49) : (i64, i64) -> i64
    %83 = "llvm.xor"(%81, %82) : (i64, i64) -> i64
    %84 = "llvm.add"(%74, %50) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %85 = "llvm.add"(%74, %83) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %86 = "llvm.add"(%85, %79) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %87 = "llvm.add"(%51, %12) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %88 = "llvm.icmp"(%87, %7) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%88, %86, %47, %48, %49, %7, %53, %54, %55, %84, %86, %47, %48, %49, %87, %53, %54, %55, %84)[^bb3, ^bb2] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 9, 9>}> : (i1, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64) -> ()
  ^bb3(%89: i64, %90: i64, %91: i64, %92: i64, %93: i64, %94: i64, %95: i64, %96: i64, %97: i64):  // 2 preds: ^bb2, ^bb3
    %98 = "llvm.add"(%93, %12) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %99 = "llvm.and"(%98, %6) : (i64, i64) -> i64
    %100 = "llvm.getelementptr"(%21, %99) <{elem_type = !llvm.array<16 x i64>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %101 = "llvm.load"(%100) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %102 = "llvm.add"(%93, %5) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %103 = "llvm.and"(%102, %6) : (i64, i64) -> i64
    %104 = "llvm.getelementptr"(%21, %103) <{elem_type = !llvm.array<16 x i64>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %105 = "llvm.load"(%104) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %106 = "llvm.call"(%101, %11) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %107 = "llvm.call"(%101, %4) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %108 = "llvm.lshr"(%101, %14) : (i64, i64) -> i64
    %109 = "llvm.xor"(%106, %108) : (i64, i64) -> i64
    %110 = "llvm.xor"(%109, %107) : (i64, i64) -> i64
    %111 = "llvm.call"(%105, %3) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %112 = "llvm.call"(%105, %2) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %113 = "llvm.lshr"(%105, %13) : (i64, i64) -> i64
    %114 = "llvm.xor"(%111, %113) : (i64, i64) -> i64
    %115 = "llvm.xor"(%114, %112) : (i64, i64) -> i64
    %116 = "llvm.add"(%93, %1) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %117 = "llvm.and"(%116, %6) : (i64, i64) -> i64
    %118 = "llvm.getelementptr"(%21, %117) <{elem_type = !llvm.array<16 x i64>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %119 = "llvm.load"(%118) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %120 = "llvm.and"(%93, %6) : (i64, i64) -> i64
    %121 = "llvm.getelementptr"(%21, %120) <{elem_type = !llvm.array<16 x i64>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %122 = "llvm.load"(%121) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %123 = "llvm.add"(%119, %110) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %124 = "llvm.add"(%123, %115) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %125 = "llvm.add"(%124, %122) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.store"(%125, %121) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %126 = "llvm.call"(%97, %16) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %127 = "llvm.call"(%97, %17) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %128 = "llvm.xor"(%127, %126) : (i64, i64) -> i64
    %129 = "llvm.call"(%97, %18) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %130 = "llvm.xor"(%128, %129) : (i64, i64) -> i64
    %131 = "llvm.and"(%96, %97) : (i64, i64) -> i64
    %132 = "llvm.xor"(%97, %19) : (i64, i64) -> i64
    %133 = "llvm.and"(%95, %132) : (i64, i64) -> i64
    %134 = "llvm.getelementptr"(%20, %93) <{elem_type = !llvm.array<80 x i64>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %135 = "llvm.load"(%134) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %136 = "llvm.or"(%133, %131) : (i64, i64) -> i64
    %137 = "llvm.add"(%136, %94) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %138 = "llvm.add"(%137, %125) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %139 = "llvm.add"(%138, %130) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %140 = "llvm.add"(%139, %135) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %141 = "llvm.call"(%89, %10) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %142 = "llvm.call"(%89, %9) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %143 = "llvm.xor"(%142, %141) : (i64, i64) -> i64
    %144 = "llvm.call"(%89, %8) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %145 = "llvm.xor"(%143, %144) : (i64, i64) -> i64
    %146 = "llvm.xor"(%90, %91) : (i64, i64) -> i64
    %147 = "llvm.and"(%89, %146) : (i64, i64) -> i64
    %148 = "llvm.and"(%90, %91) : (i64, i64) -> i64
    %149 = "llvm.xor"(%147, %148) : (i64, i64) -> i64
    %150 = "llvm.add"(%140, %92) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %151 = "llvm.add"(%140, %149) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %152 = "llvm.add"(%151, %145) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %153 = "llvm.icmp"(%98, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%153, %152, %89, %90, %91, %98, %95, %96, %97, %150)[^bb4, ^bb3] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 0, 9>}> : (i1, i64, i64, i64, i64, i64, i64, i64, i64, i64) -> ()
  ^bb4:  // pred: ^bb3
    %154 = "llvm.add"(%152, %44) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.store"(%154, %arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %155 = "llvm.add"(%89, %43) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.store"(%155, %22) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %156 = "llvm.add"(%90, %42) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.store"(%156, %23) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %157 = "llvm.add"(%91, %41) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.store"(%157, %24) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %158 = "llvm.add"(%150, %40) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.store"(%158, %25) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %159 = "llvm.add"(%97, %39) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.store"(%159, %26) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %160 = "llvm.add"(%96, %38) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.store"(%160, %27) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %161 = "llvm.add"(%95, %37) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.store"(%161, %28) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %162 = "llvm.getelementptr"(%45) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.end"(%21) <{size = 128 : i64}> : (!llvm.ptr) -> ()
    %163 = "llvm.add"(%46, %19) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %164 = "llvm.icmp"(%163, %15) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%164, %161, %160, %159, %158, %157, %156, %155, %154, %162, %163)[^bb5, ^bb1] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 0, 10>}> : (i1, i64, i64, i64, i64, i64, i64, i64, i64, !llvm.ptr, i64) -> ()
  ^bb5:  // pred: ^bb4
    "llvm.return"() : () -> ()
}
]

set_option maxRecDepth 100000 in
def fd_sha512_core_ref : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [] :=
  [sllvm_cfg_of| fd_sha512_core_ref_region with
    @fd_ulong_bswap := fd_ulong_bswap,
    @fd_ulong_rotate_right := fd_ulong_rotate_right]

private def packLE (ws : List Nat) (wbytes : Nat) : Nat :=
  (ws.zipIdx).foldl (fun acc (w, i) => acc + w * 2 ^ (8 * wbytes * i)) 0

private def kWords : List Nat := [0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
  0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
  0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
  0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
  0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
  0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
  0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
  0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
  0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
  0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
  0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

private def ivWords : List Nat := [0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b,
  0xa54ff53a5f1d36f1, 0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

private def abcBlock : List Nat := [0x61, 0x62, 0x63, 0x80] ++ List.replicate 123 0 ++ [0x18]

private def install (s : GlobalState) (n : Nat) (v : Nat) : GlobalState × Pointer :=
  let p : Pointer := ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩
  let s := s.afterAlloca (8 * n)
  ({ s with mem := s.mem.splice p (BitVec.ofNat (8 * n) v) }, p)

private def runOn (msg : List Nat) (cnt : Nat) : Option (List Nat) := Id.run do
  let s₀ : GlobalState := ⟨⟨0⟩, ⟨∅⟩, ∅⟩
  let (s₁, kp) := install s₀ 640 (packLE kWords 8)
  let s₁ := { s₁ with globals := s₁.globals.insert "fd_sha512_core_ref.K" kp }
  let (s₂, stp) := install s₁ 64 (packLE ivWords 8)
  let (s₃, bp) := install s₂ (128 * cnt) (packLE msg 1)
  let V := Ctxt.Valuation.ofHVector
    [(PoisonOr.value (BitVec.ofNat 64 cnt) : LLVM.IntW 64), PoisonOr.value bp, PoisonOr.value stp]ₕ
  match Cfg.eval 2000 fd_sha512_core_ref V s₃ with
  | some (.value (_, s')) =>
      match s'.mem.live? stp.id with
      | some blk => some ((List.range 8).map fun i => (blk.bytes.extractLsb' (64 * i) 64).toNat)
      | none => none
  | _ => none

private def abcDigest : List Nat := [0xddaf35a193617aba, 0xcc417349ae204131, 0x12e6fa4e89a97ea2,
  0x0a9eeee64b55d39a, 0x2192992a274fc1a8, 0x36ba3c23a3feebbd, 0x454d4423643ce80e, 0x2a9ac94fa54ca49f]

private def twoBlock : List Nat :=
  ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno" ++
    "ijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu").toList.map Char.toNat
    ++ [0x80] ++ List.replicate 141 0 ++ [0x03, 0x80]

private def twoBlockDigest : List Nat := [0x8e959b75dae313da, 0x8cf4f72814fc143f, 0x8f7779c6eb9f7fa1,
  0x7299aeadb6889018, 0x501d289e4900f7e4, 0x331b99dec4b5433a, 0xc7d329eeb6dd2654, 0x5e96e55b874be909]

#guard runOn abcBlock 1 == some abcDigest
#guard runOn twoBlock 2 == some twoBlockDigest

end Firedancer.Common

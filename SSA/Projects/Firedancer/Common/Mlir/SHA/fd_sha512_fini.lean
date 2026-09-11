/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/{ref,avx512}/region/fd_sha512_fini.mlir
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_memset
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_sha512_core_ref
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_ulong_bswap

namespace Firedancer.Common
open LeanMLIR SLLVM

set_option maxRecDepth 100000 in
def fd_sha512_fini_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = -128 : i8}> : () -> i8
    %2 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 112 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 127 : i64}> : () -> i64
    %5 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    %6 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 3>}> : (!llvm.ptr) -> !llvm.ptr
    %7 = "llvm.load"(%6) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag3]}> : (!llvm.ptr) -> i64
    %8 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 4>}> : (!llvm.ptr) -> !llvm.ptr
    %9 = "llvm.load"(%8) <{alignment = 16 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag4]}> : (!llvm.ptr) -> i64
    %10 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 5>}> : (!llvm.ptr) -> !llvm.ptr
    %11 = "llvm.load"(%10) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag5]}> : (!llvm.ptr) -> i64
    %12 = "llvm.getelementptr"(%arg0, %7) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%1, %12) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %13 = "llvm.add"(%7, %2) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %14 = "llvm.icmp"(%13, %3) <{predicate = 8 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%14, %13)[^bb1, ^bb2] <{branch_weights = array<i32: 1, 2000>, operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i64) -> ()
  ^bb1:  // pred: ^bb0
    %15 = "llvm.getelementptr"(%arg0, %13) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %16 = "llvm.sub"(%4, %7) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %17 = "llvm.call"(%15, %16) <{CConv = #llvm.cconv<fastcc>, callee = @fd_memset, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.call"(%5, %arg0, %2) <{CConv = #llvm.cconv<fastcc>, callee = @fd_sha512_core_ref, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.br"(%0)[^bb2] : (i64) -> ()
  ^bb2(%18: i64):  // 2 preds: ^bb0, ^bb1
    %19 = "llvm.getelementptr"(%arg0, %18) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %20 = "llvm.sub"(%3, %18) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %21 = "llvm.call"(%19, %20) <{CConv = #llvm.cconv<fastcc>, callee = @fd_memset, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %22 = "llvm.call"(%11) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_bswap, fastmathFlags = #llvm.fastmath<none>}> : (i64) -> i64
    %23 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 0, 112>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%22, %23) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %24 = "llvm.call"(%9) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_bswap, fastmathFlags = #llvm.fastmath<none>}> : (i64) -> i64
    %25 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 0, 120>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%24, %25) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    "llvm.call"(%5, %arg0, %2) <{CConv = #llvm.cconv<fastcc>, callee = @fd_sha512_core_ref, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %26 = "llvm.load"(%5) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %27 = "llvm.call"(%26) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_bswap, fastmathFlags = #llvm.fastmath<none>}> : (i64) -> i64
    "llvm.store"(%27, %arg1) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %28 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 1, 1>}> : (!llvm.ptr) -> !llvm.ptr
    %29 = "llvm.load"(%28) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %30 = "llvm.call"(%29) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_bswap, fastmathFlags = #llvm.fastmath<none>}> : (i64) -> i64
    %31 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%30, %31) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %32 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 1, 2>}> : (!llvm.ptr) -> !llvm.ptr
    %33 = "llvm.load"(%32) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %34 = "llvm.call"(%33) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_bswap, fastmathFlags = #llvm.fastmath<none>}> : (i64) -> i64
    %35 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%34, %35) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %36 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 1, 3>}> : (!llvm.ptr) -> !llvm.ptr
    %37 = "llvm.load"(%36) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %38 = "llvm.call"(%37) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_bswap, fastmathFlags = #llvm.fastmath<none>}> : (i64) -> i64
    %39 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%38, %39) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %40 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 1, 4>}> : (!llvm.ptr) -> !llvm.ptr
    %41 = "llvm.load"(%40) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %42 = "llvm.call"(%41) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_bswap, fastmathFlags = #llvm.fastmath<none>}> : (i64) -> i64
    %43 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%42, %43) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %44 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 1, 5>}> : (!llvm.ptr) -> !llvm.ptr
    %45 = "llvm.load"(%44) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %46 = "llvm.call"(%45) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_bswap, fastmathFlags = #llvm.fastmath<none>}> : (i64) -> i64
    %47 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 5>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%46, %47) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %48 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 1, 6>}> : (!llvm.ptr) -> !llvm.ptr
    %49 = "llvm.load"(%48) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %50 = "llvm.call"(%49) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_bswap, fastmathFlags = #llvm.fastmath<none>}> : (i64) -> i64
    %51 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 6>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%50, %51) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %52 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 1, 7>}> : (!llvm.ptr) -> !llvm.ptr
    %53 = "llvm.load"(%52) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %54 = "llvm.call"(%53) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_bswap, fastmathFlags = #llvm.fastmath<none>}> : (i64) -> i64
    %55 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 7>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%54, %55) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    "llvm.return"(%arg1) : (!llvm.ptr) -> ()
}
]

set_option maxRecDepth 100000 in
def fd_sha512_fini : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_sha512_fini_region with
    @fd_memset := fd_memset,
    @fd_sha512_core_ref := fd_sha512_core_ref,
    @fd_ulong_bswap := fd_ulong_bswap]

end Firedancer.Common

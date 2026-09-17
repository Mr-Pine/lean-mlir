/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/{ref,avx512}/region/fd_sha512_init.mlir
import SSA.Projects.SLLVM.Cfg

namespace Firedancer.Common
open LeanMLIR SLLVM

set_option maxRecDepth 100000 in
def fd_sha512_init_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 7640891576956012808 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = -4942790177534073029 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 4354685564936845355 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = -6534734903238641935 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 5840696475078001361 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = -7276294671716946913 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 2270897969802886507 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 6620516959819538809 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %9 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> i64
    %10 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%0, %10) <{alignment = 128 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %11 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 1, 1>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%1, %11) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %12 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 1, 2>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%2, %12) <{alignment = 16 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %13 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 1, 3>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%3, %13) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %14 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 1, 4>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%4, %14) <{alignment = 32 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %15 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 1, 5>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%5, %15) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %16 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 1, 6>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%6, %16) <{alignment = 16 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %17 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 1, 7>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%7, %17) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %18 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: 0, 3>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.intr.memset"(%18, %8, %9) <{isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

set_option maxRecDepth 100000 in
sllvm_cfg_def fd_sha512_init : Cfg (Ctxt.ofList [SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_sha512_init_region]

end Firedancer.Common

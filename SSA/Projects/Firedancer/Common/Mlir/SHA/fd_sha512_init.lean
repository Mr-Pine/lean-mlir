/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg

/-!
# `fd_sha512_init` (common)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/{ref,avx512}/region/fd_sha512_init.mlir`. The two
backends emit the same file, so the function is lifted once, here.

`fd_sha512.c`: write the eight FIPS 180-4 initial hash words into the
state's `state[8]` array and zero the three counters, returning the handle.
Straight-line: eight stores through struct-field geps, then one `memset`.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM

set_option maxRecDepth 100000 in
def fd_sha512_init_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %2 = "llvm.mlir.constant"() <{value = 7640891576956012808 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = -4942790177534073029 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 4354685564936845355 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = -6534734903238641935 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 5840696475078001361 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = -7276294671716946913 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = 2270897969802886507 : i64}> : () -> i64
    %15 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %16 = "llvm.mlir.constant"() <{value = 6620516959819538809 : i64}> : () -> i64
    %17 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %18 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %19 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> i64
    %20 = "llvm.getelementptr"(%arg0, %0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%2, %20) <{alignment = 128 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %21 = "llvm.getelementptr"(%arg0, %0, %3) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    "llvm.store"(%4, %21) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %22 = "llvm.getelementptr"(%arg0, %0, %5) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    "llvm.store"(%6, %22) <{alignment = 16 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %23 = "llvm.getelementptr"(%arg0, %0, %7) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    "llvm.store"(%8, %23) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %24 = "llvm.getelementptr"(%arg0, %0, %9) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    "llvm.store"(%10, %24) <{alignment = 32 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %25 = "llvm.getelementptr"(%arg0, %0, %11) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    "llvm.store"(%12, %25) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %26 = "llvm.getelementptr"(%arg0, %0, %13) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    "llvm.store"(%14, %26) <{alignment = 16 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %27 = "llvm.getelementptr"(%arg0, %0, %15) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    "llvm.store"(%16, %27) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %28 = "llvm.getelementptr"(%arg0, %0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 3>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memset"(%28, %18, %19) <{isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

set_option maxRecDepth 100000 in
def fd_sha512_init : Cfg (Ctxt.ofList [SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_sha512_init_region]

end Firedancer.Common

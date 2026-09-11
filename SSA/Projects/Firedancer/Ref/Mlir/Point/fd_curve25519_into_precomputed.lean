/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_add_nr
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_sub_nr
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_set
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_mul

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fd_curve25519_into_precomputed_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %3 = "llvm.mlir.constant"() <{value = dense<[1859910466990425, 932731440258426, 1072319116312658, 1815898335770999, 633789495995903]> : tensor<5xi64>}> : () -> !llvm.array<5 x i64>
    %4 = "llvm.mlir.undef"() : () -> !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>
    %5 = "llvm.insertvalue"(%4, %3) <{position = array<i64: 0>}> : (!llvm.struct<"struct.fd_f25519", (array<5 x i64>)>, !llvm.array<5 x i64>) -> !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>
    %6 = "llvm.mlir.undef"() : () -> !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>
    %7 = "llvm.insertvalue"(%6, %5) <{position = array<i64: 0>}> : (!llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>) -> !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>
    %8 = "llvm.mlir.addressof"() <{global_name = @fd_f25519_k}> : () -> !llvm.ptr
    %9 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %10 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%9) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%10) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %11 = "llvm.getelementptr"(%arg0, %1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %12 = "llvm.call"(%9, %11, %arg0) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_add_nr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %13 = "llvm.call"(%10, %11, %arg0) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sub_nr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %14 = "llvm.call"(%arg0, %10) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_set, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %15 = "llvm.call"(%11, %9) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_set, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %16 = "llvm.getelementptr"(%arg0, %1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 2>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %17 = "llvm.call"(%16, %16, %8) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.end"(%10) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%9) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

def fd_curve25519_into_precomputed : Cfg (Ctxt.ofList [SLLVM.Ty.ptr]) [] :=
  [sllvm_cfg_of| fd_curve25519_into_precomputed_region with
    @fd_f25519_add_nr := fd_f25519_add_nr,
    @fd_f25519_sub_nr := fd_f25519_sub_nr,
    @fd_f25519_set := fd_f25519_set,
    @fd_f25519_mul := fd_f25519_mul]

end Firedancer.Ref

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_add_nr
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_sqr4
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_add
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_sub
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_sub_nr

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fd_ed25519_partial_dbl_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %3 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %4 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %5 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %6 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %7 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %8 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%4) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%5) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%6) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%7) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%8) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %9 = "llvm.getelementptr"(%arg1, %1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %10 = "llvm.call"(%4, %arg1, %9) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_add_nr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %11 = "llvm.getelementptr"(%arg1, %1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 3>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.call"(%5, %arg1, %6, %9, %7, %11, %8, %4) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr4, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    %12 = "llvm.call"(%7, %7, %7) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_add, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %13 = "llvm.getelementptr"(%arg0, %1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 2>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %14 = "llvm.call"(%13, %5, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_add, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %15 = "llvm.getelementptr"(%arg0, %1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 3>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %16 = "llvm.call"(%15, %5, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sub, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %17 = "llvm.getelementptr"(%arg0, %1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %18 = "llvm.call"(%17, %7, %15) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_add_nr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %19 = "llvm.call"(%arg0, %13, %8) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sub_nr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.end"(%8) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%7) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%6) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%5) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%4) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

def fd_ed25519_partial_dbl :
    Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr])
      [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_ed25519_partial_dbl_region with
    @fd_f25519_add_nr := fd_f25519_add_nr,
    @fd_f25519_sqr4 := fd_f25519_sqr4,
    @fd_f25519_add := fd_f25519_add,
    @fd_f25519_sub := fd_f25519_sub,
    @fd_f25519_sub_nr := fd_f25519_sub_nr]

end Firedancer.Ref

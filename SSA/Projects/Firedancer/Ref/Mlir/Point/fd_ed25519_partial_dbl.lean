/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/ref/region/fd_ed25519_partial_dbl.mlir
module

public import SSA.Projects.SLLVM.Cfg
public import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_add_nr
public import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_sqr4
public import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_add
public import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_sub
public import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_sub_nr
-- callee bindings are evaluated while elaborating
public meta import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_add_nr
public meta import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_sqr4
public meta import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_add
public meta import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_sub
public meta import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_sub_nr

@[expose] public section

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fd_ed25519_partial_dbl_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %2 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %3 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %4 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %5 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%1) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%2) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%3) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%4) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%5) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %6 = "llvm.getelementptr"(%arg1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>, inbounds, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    %7 = "llvm.call"(%1, %arg1, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_add_nr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %8 = "llvm.getelementptr"(%arg1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>, inbounds, rawConstantIndices = array<i32: 0, 3>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.call"(%2, %arg1, %3, %6, %4, %8, %5, %1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr4, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    %9 = "llvm.call"(%4, %4, %4) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_add, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %10 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>, inbounds, rawConstantIndices = array<i32: 0, 2>}> : (!llvm.ptr) -> !llvm.ptr
    %11 = "llvm.call"(%10, %2, %3) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_add, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %12 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>, inbounds, rawConstantIndices = array<i32: 0, 3>}> : (!llvm.ptr) -> !llvm.ptr
    %13 = "llvm.call"(%12, %2, %3) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sub, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %14 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>, inbounds, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    %15 = "llvm.call"(%14, %4, %12) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_add_nr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %16 = "llvm.call"(%arg0, %10, %5) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sub_nr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.end"(%5) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%4) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%3) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%2) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%1) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

sllvm_cfg_def fd_ed25519_partial_dbl :
    Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr])
      [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_ed25519_partial_dbl_region with
    @fd_f25519_add_nr := fd_f25519_add_nr,
    @fd_f25519_sqr4 := fd_f25519_sqr4,
    @fd_f25519_add := fd_f25519_add,
    @fd_f25519_sub := fd_f25519_sub,
    @fd_f25519_sub_nr := fd_f25519_sub_nr]

end Firedancer.Ref

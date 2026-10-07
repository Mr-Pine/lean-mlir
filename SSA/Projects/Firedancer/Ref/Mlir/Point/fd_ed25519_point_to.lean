/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/ref/region/fd_ed25519_point_to.mlir
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_set

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fd_ed25519_point_to_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr, %arg3: !llvm.ptr, %arg4: !llvm.ptr):
    %0 = "llvm.call"(%arg0, %arg4) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_set, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %1 = "llvm.getelementptr"(%arg4) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>, inbounds, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    %2 = "llvm.call"(%arg1, %1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_set, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %3 = "llvm.getelementptr"(%arg4) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>, inbounds, rawConstantIndices = array<i32: 0, 3>}> : (!llvm.ptr) -> !llvm.ptr
    %4 = "llvm.call"(%arg2, %3) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_set, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %5 = "llvm.getelementptr"(%arg4) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>, inbounds, rawConstantIndices = array<i32: 0, 2>}> : (!llvm.ptr) -> !llvm.ptr
    %6 = "llvm.call"(%arg3, %5) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_set, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.return"() : () -> ()
}
]

sllvm_cfg_def fd_ed25519_point_to :
    Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr])
      [] :=
  [sllvm_cfg_of| fd_ed25519_point_to_region with
    @fd_f25519_set := fd_f25519_set]

end Firedancer.Ref

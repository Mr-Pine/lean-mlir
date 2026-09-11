/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_partial_dbl
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_add_final_mul
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_add_final_mul_projective

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fd_ed25519_point_dbln_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: i32):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %2 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%2) <{size = 160 : i64}> : (!llvm.ptr) -> ()
    %3 = "llvm.call"(%2, %arg1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_partial_dbl, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %4 = "llvm.icmp"(%arg2, %0) <{predicate = 4 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%4, %1)[^bb2, ^bb1] <{operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, i8) -> ()
  ^bb1:  // 2 preds: ^bb0, ^bb2
    %5 = "llvm.call"(%arg0, %2) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_add_final_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.end"(%2) <{size = 160 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
  ^bb2(%6: i8):  // 2 preds: ^bb0, ^bb2
    %7 = "llvm.call"(%arg0, %2) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_add_final_mul_projective, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %8 = "llvm.call"(%2, %arg0) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_partial_dbl, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %9 = "llvm.add"(%6, %1) <{overflowFlags = #llvm.overflow<none>}> : (i8, i8) -> i8
    %10 = "llvm.zext"(%9) : (i8) -> i32
    %11 = "llvm.icmp"(%10, %arg2) <{predicate = 6 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%11, %9)[^bb2, ^bb1] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, i8) -> ()
}
]

def fd_ed25519_point_dbln :
    Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 32, SLLVM.Ty.ptr, SLLVM.Ty.ptr])
      [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_ed25519_point_dbln_region with
    @fd_ed25519_partial_dbl := fd_ed25519_partial_dbl,
    @fd_ed25519_point_add_final_mul_projective := fd_ed25519_point_add_final_mul_projective,
    @fd_ed25519_point_add_final_mul := fd_ed25519_point_add_final_mul]

end Firedancer.Ref

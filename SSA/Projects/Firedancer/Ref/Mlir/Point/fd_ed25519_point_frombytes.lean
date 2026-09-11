/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/ref/region/fd_ed25519_point_frombytes.mlir
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_frombytes
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_sqr
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_mul
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_add
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_sub
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_neg
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_sgn
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_sqrt_ratio
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_from

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fd_ed25519_point_frombytes_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 7 : i8}> : () -> i8
    %1 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %2 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %3 = "llvm.mlir.addressof"() <{global_name = @fd_f25519_d}> : () -> !llvm.ptr
    %4 = "llvm.mlir.addressof"() <{global_name = @fd_f25519_one}> : () -> !llvm.ptr
    %5 = "llvm.mlir.zero"() : () -> !llvm.ptr
    %6 = "llvm.alloca"(%2) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %7 = "llvm.alloca"(%2) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %8 = "llvm.alloca"(%2) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %9 = "llvm.alloca"(%2) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %10 = "llvm.alloca"(%2) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%6) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%7) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%8) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %11 = "llvm.call"(%7, %arg1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_frombytes, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %12 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 31>}> : (!llvm.ptr) -> !llvm.ptr
    %13 = "llvm.load"(%12) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    "llvm.intr.lifetime.start"(%9) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%10) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %14 = "llvm.call"(%9, %7) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %15 = "llvm.call"(%10, %9, %3) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %16 = "llvm.call"(%9, %9, %4) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sub, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %17 = "llvm.call"(%10, %10, %4) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_add, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %18 = "llvm.call"(%6, %9, %10) <{CConv = #llvm.cconv<ccc>, callee = @fd_f25519_sqrt_ratio, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> i32
    %19 = "llvm.icmp"(%18, %1) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%19, %5)[^bb4, ^bb1] <{branch_weights = array<i32: 1, 2000>, operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, !llvm.ptr) -> ()
  ^bb1:  // pred: ^bb0
    %20 = "llvm.lshr"(%13, %0) : (i8, i8) -> i8
    %21 = "llvm.call"(%6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sgn, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i32
    %22 = "llvm.zext"(%20) : (i8) -> i32
    %23 = "llvm.icmp"(%21, %22) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%23)[^bb3, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb2:  // pred: ^bb1
    %24 = "llvm.call"(%6, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_neg, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.br"()[^bb3] : () -> ()
  ^bb3:  // 2 preds: ^bb1, ^bb2
    %25 = "llvm.call"(%8, %6, %7) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %26 = "llvm.call"(%arg0, %6, %7, %4, %8) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_from, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.br"(%arg0)[^bb4] : (!llvm.ptr) -> ()
  ^bb4(%27: !llvm.ptr):  // 2 preds: ^bb0, ^bb3
    "llvm.intr.lifetime.end"(%10) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%9) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%8) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%7) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%6) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"(%27) : (!llvm.ptr) -> ()
}
]

def fd_ed25519_point_frombytes :
    Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_ed25519_point_frombytes_region with
    @fd_f25519_frombytes := fd_f25519_frombytes,
    @fd_f25519_sqr := fd_f25519_sqr,
    @fd_f25519_mul := fd_f25519_mul,
    @fd_f25519_add := fd_f25519_add,
    @fd_f25519_sub := fd_f25519_sub,
    @fd_f25519_neg := fd_f25519_neg,
    @fd_f25519_sgn := fd_f25519_sgn,
    @fd_f25519_sqrt_ratio := fd_f25519_sqrt_ratio,
    @fd_ed25519_point_from := fd_ed25519_point_from]

end Firedancer.Ref

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/ref/region/fd_f25519_pow22523.mlir
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_sqr
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_mul

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fd_f25519_pow22523_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %2 = "llvm.mlir.constant"() <{value = 10 : i32}> : () -> i32
    %3 = "llvm.mlir.constant"() <{value = 20 : i32}> : () -> i32
    %4 = "llvm.mlir.constant"() <{value = 50 : i32}> : () -> i32
    %5 = "llvm.mlir.constant"() <{value = 100 : i32}> : () -> i32
    %6 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %7 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %8 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%6) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%7) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%8) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %9 = "llvm.call"(%6, %arg1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %10 = "llvm.call"(%7, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %11 = "llvm.call"(%7, %7) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %12 = "llvm.call"(%7, %arg1, %7) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %13 = "llvm.call"(%6, %6, %7) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %14 = "llvm.call"(%6, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %15 = "llvm.call"(%6, %7, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %16 = "llvm.call"(%7, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.br"(%0)[^bb2] : (i32) -> ()
  ^bb1:  // pred: ^bb2
    %17 = "llvm.call"(%6, %7, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %18 = "llvm.call"(%7, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.br"(%0)[^bb4] : (i32) -> ()
  ^bb2(%19: i32):  // 2 preds: ^bb0, ^bb2
    %20 = "llvm.call"(%7, %7) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %21 = "llvm.add"(%19, %0) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i32, i32) -> i32
    %22 = "llvm.icmp"(%21, %1) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%22, %21)[^bb1, ^bb2] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i32) -> ()
  ^bb3:  // pred: ^bb4
    %23 = "llvm.call"(%7, %7, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %24 = "llvm.call"(%8, %7) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.br"(%0)[^bb6] : (i32) -> ()
  ^bb4(%25: i32):  // 2 preds: ^bb1, ^bb4
    %26 = "llvm.call"(%7, %7) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %27 = "llvm.add"(%25, %0) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i32, i32) -> i32
    %28 = "llvm.icmp"(%27, %2) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%28, %27)[^bb3, ^bb4] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i32) -> ()
  ^bb5:  // pred: ^bb6
    %29 = "llvm.call"(%7, %8, %7) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %30 = "llvm.call"(%7, %7) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.br"(%0)[^bb8] : (i32) -> ()
  ^bb6(%31: i32):  // 2 preds: ^bb3, ^bb6
    %32 = "llvm.call"(%8, %8) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %33 = "llvm.add"(%31, %0) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i32, i32) -> i32
    %34 = "llvm.icmp"(%33, %3) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%34, %33)[^bb5, ^bb6] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i32) -> ()
  ^bb7:  // pred: ^bb8
    %35 = "llvm.call"(%6, %7, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %36 = "llvm.call"(%7, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.br"(%0)[^bb10] : (i32) -> ()
  ^bb8(%37: i32):  // 2 preds: ^bb5, ^bb8
    %38 = "llvm.call"(%7, %7) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %39 = "llvm.add"(%37, %0) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i32, i32) -> i32
    %40 = "llvm.icmp"(%39, %2) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%40, %39)[^bb7, ^bb8] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i32) -> ()
  ^bb9:  // pred: ^bb10
    %41 = "llvm.call"(%7, %7, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %42 = "llvm.call"(%8, %7) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.br"(%0)[^bb12] : (i32) -> ()
  ^bb10(%43: i32):  // 2 preds: ^bb7, ^bb10
    %44 = "llvm.call"(%7, %7) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %45 = "llvm.add"(%43, %0) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i32, i32) -> i32
    %46 = "llvm.icmp"(%45, %4) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%46, %45)[^bb9, ^bb10] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i32) -> ()
  ^bb11:  // pred: ^bb12
    %47 = "llvm.call"(%7, %8, %7) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %48 = "llvm.call"(%7, %7) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.br"(%0)[^bb14] : (i32) -> ()
  ^bb12(%49: i32):  // 2 preds: ^bb9, ^bb12
    %50 = "llvm.call"(%8, %8) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %51 = "llvm.add"(%49, %0) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i32, i32) -> i32
    %52 = "llvm.icmp"(%51, %5) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%52, %51)[^bb11, ^bb12] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i32) -> ()
  ^bb13:  // pred: ^bb14
    %53 = "llvm.call"(%6, %7, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %54 = "llvm.call"(%6, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %55 = "llvm.call"(%6, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %56 = "llvm.call"(%arg0, %6, %arg1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.end"(%8) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%7) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%6) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
  ^bb14(%57: i32):  // 2 preds: ^bb11, ^bb14
    %58 = "llvm.call"(%7, %7) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %59 = "llvm.add"(%57, %0) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i32, i32) -> i32
    %60 = "llvm.icmp"(%59, %4) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%60, %59)[^bb13, ^bb14] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i32) -> ()
}
]

sllvm_cfg_def fd_f25519_pow22523 : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_f25519_pow22523_region with
    @fd_f25519_sqr := fd_f25519_sqr,
    @fd_f25519_mul := fd_f25519_mul]

end Firedancer.Ref

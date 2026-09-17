/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/avx512/region/fd_ed25519_double_scalar_mul_base.mlir
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Common.Mlir.Scalar.fd_curve25519_scalar_wnaf
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_set
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_dbln
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_curve25519_into_precomputed
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_add_with_opts
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_add_final_mul
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_set_zero
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_partial_dbl
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_sub_with_opts
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_add_final_mul_projective

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_ed25519_double_scalar_mul_base_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr, %arg3: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %2 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %3 = "llvm.mlir.constant"() <{value = 8 : i32}> : () -> i32
    %4 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 255 : i32}> : () -> i32
    %9 = "llvm.mlir.constant"() <{value = 0 : i16}> : () -> i16
    %10 = "llvm.mlir.constant"() <{value = -1 : i32}> : () -> i32
    %11 = "llvm.mlir.constant"() <{value = 1 : i16}> : () -> i16
    %12 = "llvm.mlir.addressof"() <{global_name = @fd_ed25519_base_point_wnaf_table}> : () -> !llvm.ptr
    %13 = "llvm.alloca"(%1) <{alignment = 16 : i64, elem_type = !llvm.array<256 x i16>}> : (i32) -> !llvm.ptr
    %14 = "llvm.alloca"(%1) <{alignment = 16 : i64, elem_type = !llvm.array<256 x i16>}> : (i32) -> !llvm.ptr
    %15 = "llvm.alloca"(%1) <{alignment = 64 : i64, elem_type = !llvm.array<8 x struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>>}> : (i32) -> !llvm.ptr
    %16 = "llvm.alloca"(%1) <{alignment = 64 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>>}> : (i32) -> !llvm.ptr
    %17 = "llvm.alloca"(%1) <{alignment = 64 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%13) <{size = 512 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%13, %arg1, %2) <{CConv = #llvm.cconv<ccc>, callee = @fd_curve25519_scalar_wnaf, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i32) -> ()
    "llvm.intr.lifetime.start"(%14) <{size = 512 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%14, %arg3, %3) <{CConv = #llvm.cconv<ccc>, callee = @fd_curve25519_scalar_wnaf, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i32) -> ()
    "llvm.intr.lifetime.start"(%15) <{size = 1536 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%16) <{size = 192 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%17) <{size = 192 : i64}> : (!llvm.ptr) -> ()
    %18 = "llvm.call"(%15, %arg2) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_set, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %19 = "llvm.call"(%16, %arg2, %1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_dbln, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i32) -> !llvm.ptr
    "llvm.call"(%15) <{CConv = #llvm.cconv<fastcc>, callee = @fd_curve25519_into_precomputed, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> ()
    "llvm.br"(%4)[^bb2] : (i64) -> ()
  ^bb1:  // pred: ^bb2
    %20 = "llvm.call"(%arg0) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_set_zero, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.br"(%8)[^bb3] : (i32) -> ()
  ^bb2(%21: i64):  // 2 preds: ^bb0, ^bb2
    %22 = "llvm.add"(%21, %5) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %23 = "llvm.getelementptr"(%15, %22) <{elem_type = !llvm.array<8 x struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %24 = "llvm.call"(%17, %16, %23, %1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_add_with_opts, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, i32) -> !llvm.ptr
    %25 = "llvm.getelementptr"(%15, %21) <{elem_type = !llvm.array<8 x struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %26 = "llvm.call"(%25, %17) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_add_final_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.call"(%25) <{CConv = #llvm.cconv<fastcc>, callee = @fd_curve25519_into_precomputed, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> ()
    %27 = "llvm.add"(%21, %4) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %28 = "llvm.icmp"(%27, %7) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%28, %27)[^bb1, ^bb2] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i64) -> ()
  ^bb3(%29: i32):  // 2 preds: ^bb1, ^bb5
    %30 = "llvm.zext"(%29) : (i32) -> i64
    %31 = "llvm.getelementptr"(%13, %30) <{elem_type = !llvm.array<256 x i16>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %32 = "llvm.load"(%31) <{alignment = 2 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (!llvm.ptr) -> i16
    %33 = "llvm.icmp"(%32, %9) <{predicate = 0 : i64}> : (i16, i16) -> i1
    "llvm.cond_br"(%33)[^bb4, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb4:  // pred: ^bb3
    %34 = "llvm.getelementptr"(%14, %30) <{elem_type = !llvm.array<256 x i16>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %35 = "llvm.load"(%34) <{alignment = 2 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (!llvm.ptr) -> i16
    %36 = "llvm.icmp"(%35, %9) <{predicate = 0 : i64}> : (i16, i16) -> i1
    "llvm.cond_br"(%36)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb5:  // pred: ^bb4
    %37 = "llvm.add"(%29, %10) <{overflowFlags = #llvm.overflow<nsw>}> : (i32, i32) -> i32
    %38 = "llvm.icmp"(%29, %0) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%38, %37)[^bb19, ^bb3] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i32) -> ()
  ^bb6:  // 2 preds: ^bb3, ^bb4
    %39 = "llvm.icmp"(%29, %10) <{predicate = 4 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%39)[^bb7, ^bb19] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb7:  // pred: ^bb6
    %40 = "llvm.zext"(%29) : (i32) -> i64
    "llvm.br"(%40)[^bb8] : (i64) -> ()
  ^bb8(%41: i64):  // 2 preds: ^bb7, ^bb18
    %42 = "llvm.call"(%17, %arg0) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_partial_dbl, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %43 = "llvm.getelementptr"(%13, %41) <{elem_type = !llvm.array<256 x i16>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %44 = "llvm.load"(%43) <{alignment = 2 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (!llvm.ptr) -> i16
    %45 = "llvm.icmp"(%44, %9) <{predicate = 4 : i64}> : (i16, i16) -> i1
    "llvm.cond_br"(%45)[^bb9, ^bb10] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb9:  // pred: ^bb8
    %46 = "llvm.call"(%arg0, %17) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_add_final_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %47 = "llvm.lshr"(%44, %11) : (i16, i16) -> i16
    %48 = "llvm.zext"(%47) : (i16) -> i64
    %49 = "llvm.getelementptr"(%15, %48) <{elem_type = !llvm.array<8 x struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %50 = "llvm.call"(%17, %arg0, %49, %1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_add_with_opts, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, i32) -> !llvm.ptr
    "llvm.br"()[^bb12] : () -> ()
  ^bb10:  // pred: ^bb8
    %51 = "llvm.icmp"(%44, %9) <{predicate = 2 : i64}> : (i16, i16) -> i1
    "llvm.cond_br"(%51)[^bb11, ^bb12] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb11:  // pred: ^bb10
    %52 = "llvm.call"(%arg0, %17) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_add_final_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %53 = "llvm.sub"(%9, %44) <{overflowFlags = #llvm.overflow<none>}> : (i16, i16) -> i16
    %54 = "llvm.lshr"(%53, %11) : (i16, i16) -> i16
    %55 = "llvm.zext"(%54) : (i16) -> i64
    %56 = "llvm.getelementptr"(%15, %55) <{elem_type = !llvm.array<8 x struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %57 = "llvm.call"(%17, %arg0, %56, %1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_sub_with_opts, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, i32) -> !llvm.ptr
    "llvm.br"()[^bb12] : () -> ()
  ^bb12:  // 3 preds: ^bb9, ^bb10, ^bb11
    %58 = "llvm.getelementptr"(%14, %41) <{elem_type = !llvm.array<256 x i16>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %59 = "llvm.load"(%58) <{alignment = 2 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (!llvm.ptr) -> i16
    %60 = "llvm.icmp"(%59, %9) <{predicate = 4 : i64}> : (i16, i16) -> i1
    "llvm.cond_br"(%60)[^bb13, ^bb14] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb13:  // pred: ^bb12
    %61 = "llvm.call"(%arg0, %17) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_add_final_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %62 = "llvm.lshr"(%59, %11) : (i16, i16) -> i16
    %63 = "llvm.zext"(%62) : (i16) -> i64
    %64 = "llvm.getelementptr"(%12, %63) <{elem_type = !llvm.array<128 x struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %65 = "llvm.call"(%17, %arg0, %64, %1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_add_with_opts, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, i32) -> !llvm.ptr
    "llvm.br"()[^bb16] : () -> ()
  ^bb14:  // pred: ^bb12
    %66 = "llvm.icmp"(%59, %9) <{predicate = 2 : i64}> : (i16, i16) -> i1
    "llvm.cond_br"(%66)[^bb15, ^bb16] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb15:  // pred: ^bb14
    %67 = "llvm.call"(%arg0, %17) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_add_final_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %68 = "llvm.sub"(%9, %59) <{overflowFlags = #llvm.overflow<none>}> : (i16, i16) -> i16
    %69 = "llvm.lshr"(%68, %11) : (i16, i16) -> i16
    %70 = "llvm.zext"(%69) : (i16) -> i64
    %71 = "llvm.getelementptr"(%12, %70) <{elem_type = !llvm.array<128 x struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %72 = "llvm.call"(%17, %arg0, %71, %1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_sub_with_opts, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, i32) -> !llvm.ptr
    "llvm.br"()[^bb16] : () -> ()
  ^bb16:  // 3 preds: ^bb13, ^bb14, ^bb15
    %73 = "llvm.icmp"(%41, %6) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%73)[^bb17, ^bb18] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb17:  // pred: ^bb16
    %74 = "llvm.call"(%arg0, %17) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_add_final_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.br"()[^bb19] : () -> ()
  ^bb18:  // pred: ^bb16
    %75 = "llvm.call"(%arg0, %17) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_add_final_mul_projective, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %76 = "llvm.add"(%41, %5) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %77 = "llvm.icmp"(%41, %6) <{predicate = 4 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%77, %76)[^bb8, ^bb19] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, i64) -> ()
  ^bb19:  // 4 preds: ^bb5, ^bb6, ^bb17, ^bb18
    "llvm.intr.lifetime.end"(%17) <{size = 192 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%16) <{size = 192 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%15) <{size = 1536 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%14) <{size = 512 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%13) <{size = 512 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

sllvm_cfg_def fd_ed25519_double_scalar_mul_base :
    Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr])
      [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_ed25519_double_scalar_mul_base_region with
    @fd_curve25519_scalar_wnaf := Common.fd_curve25519_scalar_wnaf,
    @fd_ed25519_point_set := fd_ed25519_point_set,
    @fd_ed25519_point_dbln := fd_ed25519_point_dbln,
    @fd_curve25519_into_precomputed := fd_curve25519_into_precomputed,
    @fd_ed25519_point_add_with_opts := fd_ed25519_point_add_with_opts,
    @fd_ed25519_point_add_final_mul := fd_ed25519_point_add_final_mul,
    @fd_ed25519_point_set_zero := fd_ed25519_point_set_zero,
    @fd_ed25519_partial_dbl := fd_ed25519_partial_dbl,
    @fd_ed25519_point_sub_with_opts := fd_ed25519_point_sub_with_opts,
    @fd_ed25519_point_add_final_mul_projective := fd_ed25519_point_add_final_mul_projective]

end Firedancer.Avx512

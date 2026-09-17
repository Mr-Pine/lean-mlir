/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/ref/region/fd_ed25519_double_scalar_mul_base.mlir
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Common.Mlir.Scalar.fd_curve25519_scalar_wnaf
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_set
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_dbln
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_curve25519_into_precomputed
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_add_with_opts
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_add_final_mul
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_set_zero
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_partial_dbl
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_sub_with_opts
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_add_final_mul_projective

namespace Firedancer.Ref
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
    %12 = "llvm.mlir.constant"() <{value = -1 : i16}> : () -> i16
    %13 = "llvm.mlir.addressof"() <{global_name = @fd_ed25519_base_point_wnaf_table}> : () -> !llvm.ptr
    %14 = "llvm.alloca"(%1) <{alignment = 16 : i64, elem_type = !llvm.array<256 x i16>}> : (i32) -> !llvm.ptr
    %15 = "llvm.alloca"(%1) <{alignment = 16 : i64, elem_type = !llvm.array<256 x i16>}> : (i32) -> !llvm.ptr
    %16 = "llvm.alloca"(%1) <{alignment = 16 : i64, elem_type = !llvm.array<8 x struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>>}> : (i32) -> !llvm.ptr
    %17 = "llvm.alloca"(%1) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>>}> : (i32) -> !llvm.ptr
    %18 = "llvm.alloca"(%1) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%14) <{size = 512 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%14, %arg1, %2) <{CConv = #llvm.cconv<ccc>, callee = @fd_curve25519_scalar_wnaf, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i32) -> ()
    "llvm.intr.lifetime.start"(%15) <{size = 512 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%15, %arg3, %3) <{CConv = #llvm.cconv<ccc>, callee = @fd_curve25519_scalar_wnaf, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i32) -> ()
    "llvm.intr.lifetime.start"(%16) <{size = 1280 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%17) <{size = 160 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%18) <{size = 160 : i64}> : (!llvm.ptr) -> ()
    %19 = "llvm.call"(%16, %arg2) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_set, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %20 = "llvm.call"(%17, %arg2, %1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_dbln, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i32) -> !llvm.ptr
    "llvm.call"(%16) <{CConv = #llvm.cconv<fastcc>, callee = @fd_curve25519_into_precomputed, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> ()
    "llvm.br"(%4)[^bb2] : (i64) -> ()
  ^bb1:  // pred: ^bb2
    %21 = "llvm.call"(%arg0) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_set_zero, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.br"(%8)[^bb3] : (i32) -> ()
  ^bb2(%22: i64):  // 2 preds: ^bb0, ^bb2
    %23 = "llvm.add"(%22, %5) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %24 = "llvm.getelementptr"(%16, %23) <{elem_type = !llvm.array<8 x struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %25 = "llvm.icmp"(%22, %4) <{predicate = 0 : i64}> : (i64, i64) -> i1
    %26 = "llvm.zext"(%25) : (i1) -> i32
    %27 = "llvm.call"(%18, %17, %24, %26, %1, %1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_add_with_opts, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, i32, i32, i32) -> !llvm.ptr
    %28 = "llvm.getelementptr"(%16, %22) <{elem_type = !llvm.array<8 x struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %29 = "llvm.call"(%28, %18) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_add_final_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.call"(%28) <{CConv = #llvm.cconv<fastcc>, callee = @fd_curve25519_into_precomputed, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> ()
    %30 = "llvm.add"(%22, %4) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %31 = "llvm.icmp"(%30, %7) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%31, %30)[^bb1, ^bb2] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i64) -> ()
  ^bb3(%32: i32):  // 2 preds: ^bb1, ^bb5
    %33 = "llvm.zext"(%32) : (i32) -> i64
    %34 = "llvm.getelementptr"(%14, %33) <{elem_type = !llvm.array<256 x i16>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %35 = "llvm.load"(%34) <{alignment = 2 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (!llvm.ptr) -> i16
    %36 = "llvm.icmp"(%35, %9) <{predicate = 0 : i64}> : (i16, i16) -> i1
    "llvm.cond_br"(%36)[^bb4, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb4:  // pred: ^bb3
    %37 = "llvm.getelementptr"(%15, %33) <{elem_type = !llvm.array<256 x i16>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %38 = "llvm.load"(%37) <{alignment = 2 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (!llvm.ptr) -> i16
    %39 = "llvm.icmp"(%38, %9) <{predicate = 0 : i64}> : (i16, i16) -> i1
    "llvm.cond_br"(%39)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb5:  // pred: ^bb4
    %40 = "llvm.add"(%32, %10) <{overflowFlags = #llvm.overflow<nsw>}> : (i32, i32) -> i32
    %41 = "llvm.icmp"(%32, %0) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%41, %40)[^bb19, ^bb3] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i32) -> ()
  ^bb6:  // 2 preds: ^bb3, ^bb4
    %42 = "llvm.icmp"(%32, %10) <{predicate = 4 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%42)[^bb7, ^bb19] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb7:  // pred: ^bb6
    %43 = "llvm.zext"(%32) : (i32) -> i64
    "llvm.br"(%43)[^bb8] : (i64) -> ()
  ^bb8(%44: i64):  // 2 preds: ^bb7, ^bb18
    %45 = "llvm.call"(%18, %arg0) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_partial_dbl, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %46 = "llvm.getelementptr"(%14, %44) <{elem_type = !llvm.array<256 x i16>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %47 = "llvm.load"(%46) <{alignment = 2 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (!llvm.ptr) -> i16
    %48 = "llvm.icmp"(%47, %9) <{predicate = 4 : i64}> : (i16, i16) -> i1
    "llvm.cond_br"(%48)[^bb9, ^bb10] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb9:  // pred: ^bb8
    %49 = "llvm.call"(%arg0, %18) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_add_final_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %50 = "llvm.lshr"(%47, %11) : (i16, i16) -> i16
    %51 = "llvm.zext"(%50) : (i16) -> i64
    %52 = "llvm.getelementptr"(%16, %51) <{elem_type = !llvm.array<8 x struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %53 = "llvm.icmp"(%47, %11) <{predicate = 0 : i64}> : (i16, i16) -> i1
    %54 = "llvm.zext"(%53) : (i1) -> i32
    %55 = "llvm.call"(%18, %arg0, %52, %54, %1, %1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_add_with_opts, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, i32, i32, i32) -> !llvm.ptr
    "llvm.br"()[^bb12] : () -> ()
  ^bb10:  // pred: ^bb8
    %56 = "llvm.icmp"(%47, %9) <{predicate = 2 : i64}> : (i16, i16) -> i1
    "llvm.cond_br"(%56)[^bb11, ^bb12] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb11:  // pred: ^bb10
    %57 = "llvm.call"(%arg0, %18) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_add_final_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %58 = "llvm.sub"(%9, %47) <{overflowFlags = #llvm.overflow<none>}> : (i16, i16) -> i16
    %59 = "llvm.lshr"(%58, %11) : (i16, i16) -> i16
    %60 = "llvm.zext"(%59) : (i16) -> i64
    %61 = "llvm.getelementptr"(%16, %60) <{elem_type = !llvm.array<8 x struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %62 = "llvm.icmp"(%47, %12) <{predicate = 0 : i64}> : (i16, i16) -> i1
    %63 = "llvm.zext"(%62) : (i1) -> i32
    %64 = "llvm.call"(%18, %arg0, %61, %63, %1, %1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_sub_with_opts, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, i32, i32, i32) -> !llvm.ptr
    "llvm.br"()[^bb12] : () -> ()
  ^bb12:  // 3 preds: ^bb9, ^bb10, ^bb11
    %65 = "llvm.getelementptr"(%15, %44) <{elem_type = !llvm.array<256 x i16>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %66 = "llvm.load"(%65) <{alignment = 2 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (!llvm.ptr) -> i16
    %67 = "llvm.icmp"(%66, %9) <{predicate = 4 : i64}> : (i16, i16) -> i1
    "llvm.cond_br"(%67)[^bb13, ^bb14] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb13:  // pred: ^bb12
    %68 = "llvm.call"(%arg0, %18) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_add_final_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %69 = "llvm.lshr"(%66, %11) : (i16, i16) -> i16
    %70 = "llvm.zext"(%69) : (i16) -> i64
    %71 = "llvm.getelementptr"(%13, %70) <{elem_type = !llvm.array<128 x struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %72 = "llvm.call"(%18, %arg0, %71, %1, %1, %1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_add_with_opts, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, i32, i32, i32) -> !llvm.ptr
    "llvm.br"()[^bb16] : () -> ()
  ^bb14:  // pred: ^bb12
    %73 = "llvm.icmp"(%66, %9) <{predicate = 2 : i64}> : (i16, i16) -> i1
    "llvm.cond_br"(%73)[^bb15, ^bb16] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb15:  // pred: ^bb14
    %74 = "llvm.call"(%arg0, %18) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_add_final_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %75 = "llvm.sub"(%9, %66) <{overflowFlags = #llvm.overflow<none>}> : (i16, i16) -> i16
    %76 = "llvm.lshr"(%75, %11) : (i16, i16) -> i16
    %77 = "llvm.zext"(%76) : (i16) -> i64
    %78 = "llvm.getelementptr"(%13, %77) <{elem_type = !llvm.array<128 x struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>>, inbounds, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %79 = "llvm.call"(%18, %arg0, %78, %1, %1, %1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_sub_with_opts, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, i32, i32, i32) -> !llvm.ptr
    "llvm.br"()[^bb16] : () -> ()
  ^bb16:  // 3 preds: ^bb13, ^bb14, ^bb15
    %80 = "llvm.icmp"(%44, %6) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%80)[^bb17, ^bb18] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb17:  // pred: ^bb16
    %81 = "llvm.call"(%arg0, %18) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_add_final_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.br"()[^bb19] : () -> ()
  ^bb18:  // pred: ^bb16
    %82 = "llvm.call"(%arg0, %18) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_add_final_mul_projective, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %83 = "llvm.add"(%44, %5) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %84 = "llvm.icmp"(%44, %6) <{predicate = 4 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%84, %83)[^bb8, ^bb19] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, i64) -> ()
  ^bb19:  // 4 preds: ^bb5, ^bb6, ^bb17, ^bb18
    "llvm.intr.lifetime.end"(%18) <{size = 160 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%17) <{size = 160 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%16) <{size = 1280 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%15) <{size = 512 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%14) <{size = 512 : i64}> : (!llvm.ptr) -> ()
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

end Firedancer.Ref

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/ref/region/fd_ed25519_verify.mlir
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Common.Mlir.Scalar.fd_curve25519_scalar_validate
import SSA.Projects.Firedancer.Common.Mlir.Scalar.fd_curve25519_scalar_reduce
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_sha512_init
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_sha512_append
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_sha512_fini
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_frombytes_2x
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_affine_is_small_order
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_neg
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_double_scalar_mul_base
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_eq_z1

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fd_ed25519_verify_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: i64, %arg2: !llvm.ptr, %arg3: !llvm.ptr, %arg4: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = -3 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = -2 : i32}> : () -> i32
    %2 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %3 = "llvm.mlir.constant"() <{value = -1 : i32}> : () -> i32
    %4 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %5 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %6 = "llvm.mlir.zero"() : () -> !llvm.ptr
    %7 = "llvm.alloca"(%4) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>>}> : (i32) -> !llvm.ptr
    %8 = "llvm.alloca"(%4) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>>}> : (i32) -> !llvm.ptr
    %9 = "llvm.alloca"(%4) <{alignment = 16 : i64, elem_type = !llvm.array<64 x i8>}> : (i32) -> !llvm.ptr
    %10 = "llvm.alloca"(%4) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>>}> : (i32) -> !llvm.ptr
    %11 = "llvm.getelementptr"(%arg2) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 32>}> : (!llvm.ptr) -> !llvm.ptr
    %12 = "llvm.call"(%11) <{CConv = #llvm.cconv<fastcc>, callee = @fd_curve25519_scalar_validate, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> !llvm.ptr
    %13 = "llvm.icmp"(%12, %6) <{predicate = 0 : i64}> : (!llvm.ptr, !llvm.ptr) -> i1
    "llvm.cond_br"(%13, %3)[^bb7, ^bb1] <{branch_weights = array<i32: 1, 2000>, operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, i32) -> ()
  ^bb1:  // pred: ^bb0
    "llvm.intr.lifetime.start"(%7) <{size = 160 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%8) <{size = 160 : i64}> : (!llvm.ptr) -> ()
    %14 = "llvm.call"(%7, %arg3, %8, %arg2) <{CConv = #llvm.cconv<ccc>, callee = @fd_ed25519_point_frombytes_2x, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr) -> i32
    %15 = "llvm.icmp"(%14, %2) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%15)[^bb3, ^bb2] <{branch_weights = array<i32: 2000, 1>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb2:  // pred: ^bb1
    %16 = "llvm.icmp"(%14, %3) <{predicate = 0 : i64}> : (i32, i32) -> i1
    %17 = "llvm.select"(%16, %1, %3) <{fastmathFlags = #llvm.fastmath<none>}> : (i1, i32, i32) -> i32
    "llvm.br"(%17)[^bb6] : (i32) -> ()
  ^bb3:  // pred: ^bb1
    %18 = "llvm.call"(%7) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_affine_is_small_order, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i32
    %19 = "llvm.icmp"(%18, %2) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%19, %1)[^bb4, ^bb6] <{branch_weights = array<i32: 2000, 1>, operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i32) -> ()
  ^bb4:  // pred: ^bb3
    %20 = "llvm.call"(%8) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_affine_is_small_order, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i32
    %21 = "llvm.icmp"(%20, %2) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%21, %3)[^bb5, ^bb6] <{branch_weights = array<i32: 2000, 1>, operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i32) -> ()
  ^bb5:  // pred: ^bb4
    "llvm.intr.lifetime.start"(%9) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %22 = "llvm.call"(%arg4) <{CConv = #llvm.cconv<ccc>, callee = @fd_sha512_init, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> !llvm.ptr
    %23 = "llvm.call"(%arg4, %arg2, %5) <{CConv = #llvm.cconv<ccc>, callee = @fd_sha512_append, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i64) -> !llvm.ptr
    %24 = "llvm.call"(%arg4, %arg3, %5) <{CConv = #llvm.cconv<ccc>, callee = @fd_sha512_append, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i64) -> !llvm.ptr
    %25 = "llvm.call"(%arg4, %arg0, %arg1) <{CConv = #llvm.cconv<ccc>, callee = @fd_sha512_append, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i64) -> !llvm.ptr
    %26 = "llvm.call"(%arg4, %9) <{CConv = #llvm.cconv<ccc>, callee = @fd_sha512_fini, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %27 = "llvm.call"(%9, %9) <{CConv = #llvm.cconv<ccc>, callee = @fd_curve25519_scalar_reduce, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%10) <{size = 160 : i64}> : (!llvm.ptr) -> ()
    %28 = "llvm.call"(%7, %7) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_neg, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %29 = "llvm.call"(%10, %9, %7, %11) <{CConv = #llvm.cconv<ccc>, callee = @fd_ed25519_double_scalar_mul_base, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %30 = "llvm.call"(%10, %8) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_eq_z1, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> i32
    %31 = "llvm.icmp"(%30, %2) <{predicate = 0 : i64}> : (i32, i32) -> i1
    %32 = "llvm.select"(%31, %0, %2) <{fastmathFlags = #llvm.fastmath<none>}> : (i1, i32, i32) -> i32
    "llvm.intr.lifetime.end"(%10) <{size = 160 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%9) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.br"(%32)[^bb6] : (i32) -> ()
  ^bb6(%33: i32):  // 4 preds: ^bb2, ^bb3, ^bb4, ^bb5
    "llvm.intr.lifetime.end"(%8) <{size = 160 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%7) <{size = 160 : i64}> : (!llvm.ptr) -> ()
    "llvm.br"(%33)[^bb7] : (i32) -> ()
  ^bb7(%34: i32):  // 2 preds: ^bb0, ^bb6
    "llvm.return"(%34) : (i32) -> ()
}
]

sllvm_cfg_def fd_ed25519_verify :
    Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr])
      [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg_of| fd_ed25519_verify_region with
    @fd_curve25519_scalar_validate := Common.fd_curve25519_scalar_validate,
    @fd_ed25519_point_frombytes_2x := fd_ed25519_point_frombytes_2x,
    @fd_ed25519_affine_is_small_order := fd_ed25519_affine_is_small_order,
    @fd_sha512_init := Common.fd_sha512_init,
    @fd_sha512_append := Common.fd_sha512_append,
    @fd_sha512_fini := Common.fd_sha512_fini,
    @fd_curve25519_scalar_reduce := Common.fd_curve25519_scalar_reduce,
    @fd_ed25519_point_neg := fd_ed25519_point_neg,
    @fd_ed25519_double_scalar_mul_base := fd_ed25519_double_scalar_mul_base,
    @fd_ed25519_point_eq_z1 := fd_ed25519_point_eq_z1]

end Firedancer.Ref

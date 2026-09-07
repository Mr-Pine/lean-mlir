/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

/-!
# `fd_ed25519_point_frombytes` (ref)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/ref/region/fd_ed25519_point_frombytes.mlir`: RFC 8032
§5.1.3 point decompression.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fd_ed25519_point_frombytes_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 31 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = dense<[929955233495203, 466365720129213, 1662059464998953, 2033849074728123, 1442794654840575]> : tensor<5xi64>}> : () -> !llvm.array<5 x i64>
    %3 = "llvm.mlir.undef"() : () -> !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>
    %4 = "llvm.insertvalue"(%3, %2) <{position = array<i64: 0>}> : (!llvm.struct<"struct.fd_f25519", (array<5 x i64>)>, !llvm.array<5 x i64>) -> !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>
    %5 = "llvm.mlir.undef"() : () -> !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>
    %6 = "llvm.insertvalue"(%5, %4) <{position = array<i64: 0>}> : (!llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>) -> !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>
    %7 = "llvm.mlir.addressof"() <{global_name = @fd_f25519_d}> : () -> !llvm.ptr
    %8 = "llvm.mlir.constant"() <{value = dense<[1, 0, 0, 0, 0]> : tensor<5xi64>}> : () -> !llvm.array<5 x i64>
    %9 = "llvm.mlir.undef"() : () -> !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>
    %10 = "llvm.insertvalue"(%9, %8) <{position = array<i64: 0>}> : (!llvm.struct<"struct.fd_f25519", (array<5 x i64>)>, !llvm.array<5 x i64>) -> !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>
    %11 = "llvm.mlir.undef"() : () -> !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>
    %12 = "llvm.insertvalue"(%11, %10) <{position = array<i64: 0>}> : (!llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>) -> !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>
    %13 = "llvm.mlir.addressof"() <{global_name = @fd_f25519_one}> : () -> !llvm.ptr
    %14 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %15 = "llvm.mlir.zero"() : () -> !llvm.ptr
    %16 = "llvm.mlir.constant"() <{value = 7 : i8}> : () -> i8
    %17 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %18 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %19 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %20 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %21 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%17) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%18) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%19) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %22 = "llvm.call"(%18, %arg1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_frombytes, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %23 = "llvm.getelementptr"(%arg1, %1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %24 = "llvm.load"(%23) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    "llvm.intr.lifetime.start"(%20) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%21) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %25 = "llvm.call"(%20, %18) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %26 = "llvm.call"(%21, %20, %7) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %27 = "llvm.call"(%20, %20, %13) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sub, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %28 = "llvm.call"(%21, %21, %13) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_add, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %29 = "llvm.call"(%17, %20, %21) <{CConv = #llvm.cconv<ccc>, callee = @fd_f25519_sqrt_ratio, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> i32
    %30 = "llvm.icmp"(%29, %14) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%30, %15)[^bb4, ^bb1] <{branch_weights = array<i32: 1, 2000>, operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, !llvm.ptr) -> ()
  ^bb1:  // pred: ^bb0
    %31 = "llvm.lshr"(%24, %16) : (i8, i8) -> i8
    %32 = "llvm.call"(%17) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sgn, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i32
    %33 = "llvm.zext"(%31) : (i8) -> i32
    %34 = "llvm.icmp"(%32, %33) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%34)[^bb3, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb2:  // pred: ^bb1
    %35 = "llvm.call"(%17, %17) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_neg, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.br"()[^bb3] : () -> ()
  ^bb3:  // 2 preds: ^bb1, ^bb2
    %36 = "llvm.call"(%19, %17, %18) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %37 = "llvm.call"(%arg0, %17, %18, %13, %19) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_from, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.br"(%arg0)[^bb4] : (!llvm.ptr) -> ()
  ^bb4(%38: !llvm.ptr):  // 2 preds: ^bb0, ^bb3
    "llvm.intr.lifetime.end"(%21) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%20) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%19) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%18) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%17) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"(%38) : (!llvm.ptr) -> ()
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

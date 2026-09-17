/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/avx512/region/fd_ed25519_point_to.mlir
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.SLLVM.Dialect

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_ed25519_point_to_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr, %arg3: !llvm.ptr, %arg4: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = dense<[2, 3, 10, 6, 7, 14, 9, 9]> : vector<8xi64>}> : () -> vector<8xi64>
    %1 = "llvm.mlir.constant"() <{value = dense<[0, 1, 8, 4, 5, 12, 9, 9]> : vector<8xi64>}> : () -> vector<8xi64>
    %2 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %3 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %4 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %5 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %6 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %7 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %8 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %10 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %11 = "llvm.mlir.poison"() : () -> i64
    %12 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %13 = "llvm.insertelement"(%12, %8, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %14 = "llvm.insertelement"(%13, %11, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %15 = "llvm.insertelement"(%14, %8, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %16 = "llvm.insertelement"(%15, %11, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %17 = "llvm.insertelement"(%16, %8, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %18 = "llvm.insertelement"(%17, %11, %4) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %19 = "llvm.insertelement"(%18, %8, %3) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %20 = "llvm.insertelement"(%19, %11, %2) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %21 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %22 = "llvm.insertelement"(%21, %11, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %23 = "llvm.insertelement"(%22, %8, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %24 = "llvm.insertelement"(%23, %11, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %25 = "llvm.insertelement"(%24, %8, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %26 = "llvm.insertelement"(%25, %11, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %27 = "llvm.insertelement"(%26, %8, %4) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %28 = "llvm.insertelement"(%27, %11, %3) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %29 = "llvm.insertelement"(%28, %8, %2) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %30 = "llvm.load"(%arg4) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %31 = "llvm.getelementptr"(%arg4) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    %32 = "llvm.load"(%31) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %33 = "llvm.getelementptr"(%arg4) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 2>}> : (!llvm.ptr) -> !llvm.ptr
    %34 = "llvm.load"(%33) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %35 = "llvm.shufflevector"(%30, %32) <{mask = array<i32: 0, 8, 2, 10, 4, 12, 6, 14>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %36 = "llvm.shufflevector"(%30, %32) <{mask = array<i32: 1, 9, 3, 11, 5, 13, 7, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %37 = "llvm.shufflevector"(%34, %20) <{mask = array<i32: 0, 8, 2, 10, 4, 12, 6, 14>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %38 = "llvm.shufflevector"(%34, %29) <{mask = array<i32: 1, 9, 3, 11, 5, 13, 7, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %39 = "x86vector.avx512.intr.vpermi2var.q.512"(%35, %1, %37) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%39, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %40 = "x86vector.avx512.intr.vpermi2var.q.512"(%36, %1, %38) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%40, %arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %41 = "x86vector.avx512.intr.vpermi2var.q.512"(%35, %0, %37) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%41, %arg2) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %42 = "x86vector.avx512.intr.vpermi2var.q.512"(%36, %0, %38) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%42, %arg3) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

sllvm_cfg_def fd_ed25519_point_to :
    Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr])
      [] :=
  [sllvm_cfg_of| fd_ed25519_point_to_region]

end Firedancer.Avx512

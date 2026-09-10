/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.SLLVM.Dialect

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_ed25519_point_to_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr, %arg3: !llvm.ptr, %arg4: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %2 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %3 = "llvm.mlir.poison"() : () -> i64
    %4 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %5 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %6 = "llvm.insertelement"(%4, %0, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %7 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %8 = "llvm.insertelement"(%6, %3, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %9 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %10 = "llvm.insertelement"(%8, %0, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %11 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %12 = "llvm.insertelement"(%10, %3, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %13 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %14 = "llvm.insertelement"(%12, %0, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %15 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %16 = "llvm.insertelement"(%14, %3, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %17 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %18 = "llvm.insertelement"(%16, %0, %17) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %19 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %20 = "llvm.insertelement"(%18, %3, %19) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %21 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %22 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %23 = "llvm.insertelement"(%21, %3, %22) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %24 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %25 = "llvm.insertelement"(%23, %0, %24) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %26 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %27 = "llvm.insertelement"(%25, %3, %26) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %28 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %29 = "llvm.insertelement"(%27, %0, %28) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %30 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %31 = "llvm.insertelement"(%29, %3, %30) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %32 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %33 = "llvm.insertelement"(%31, %0, %32) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %34 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %35 = "llvm.insertelement"(%33, %3, %34) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %36 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %37 = "llvm.insertelement"(%35, %0, %36) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %38 = "llvm.mlir.constant"() <{value = dense<[0, 1, 8, 4, 5, 12, 9, 9]> : vector<8xi64>}> : () -> vector<8xi64>
    %39 = "llvm.mlir.constant"() <{value = dense<[2, 3, 10, 6, 7, 14, 9, 9]> : vector<8xi64>}> : () -> vector<8xi64>
    %40 = "llvm.load"(%arg4) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %41 = "llvm.getelementptr"(%arg4, %0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %42 = "llvm.load"(%41) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %43 = "llvm.getelementptr"(%arg4, %0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 2>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %44 = "llvm.load"(%43) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %45 = "llvm.shufflevector"(%40, %42) <{mask = array<i32: 0, 8, 2, 10, 4, 12, 6, 14>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %46 = "llvm.shufflevector"(%40, %42) <{mask = array<i32: 1, 9, 3, 11, 5, 13, 7, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %47 = "llvm.shufflevector"(%44, %20) <{mask = array<i32: 0, 8, 2, 10, 4, 12, 6, 14>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %48 = "llvm.shufflevector"(%44, %37) <{mask = array<i32: 1, 9, 3, 11, 5, 13, 7, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %49 = "x86vector.avx512.intr.vpermi2var.q.512"(%45, %38, %47) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%49, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %50 = "x86vector.avx512.intr.vpermi2var.q.512"(%46, %38, %48) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%50, %arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %51 = "x86vector.avx512.intr.vpermi2var.q.512"(%45, %39, %47) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%51, %arg2) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %52 = "x86vector.avx512.intr.vpermi2var.q.512"(%46, %39, %48) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%52, %arg3) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

def fd_ed25519_point_to :
    Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr])
      [] :=
  [sllvm_cfg_of| fd_ed25519_point_to_region]

end Firedancer.Avx512

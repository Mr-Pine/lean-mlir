/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/avx512/region/fd_r43x6_ge_is_eq.mlir
module

public import SSA.Projects.SLLVM.Dialect
public import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_quad_mul_fast
public import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_is_nonzero
-- callee bindings are evaluated while elaborating
public meta import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_quad_mul_fast
public meta import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_is_nonzero

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_r43x6_ge_is_eq_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: vector<8xi64>, %arg1: vector<8xi64>, %arg2: vector<8xi64>, %arg3: vector<8xi64>, %arg4: vector<8xi64>, %arg5: vector<8xi64>):
    %0 = "llvm.mlir.constant"() <{value = -1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = dense<[8796093022189, 8796093022207, 8796093022207, 8796093022207, 8796093022207, 1099511627775, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %2 = "llvm.mlir.constant"() <{value = dense<[2, 3, 10, 6, 7, 14, 9, 9]> : vector<8xi64>}> : () -> vector<8xi64>
    %3 = "llvm.mlir.constant"() <{value = dense<[0, 1, 8, 4, 5, 12, 9, 9]> : vector<8xi64>}> : () -> vector<8xi64>
    %4 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %5 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %6 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %7 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %8 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %9 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %10 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %11 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %13 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %14 = "llvm.mlir.poison"() : () -> i64
    %15 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %16 = "llvm.insertelement"(%15, %11, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %17 = "llvm.insertelement"(%16, %14, %12) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %18 = "llvm.insertelement"(%17, %11, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %19 = "llvm.insertelement"(%18, %14, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %20 = "llvm.insertelement"(%19, %11, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %21 = "llvm.insertelement"(%20, %14, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %22 = "llvm.insertelement"(%21, %11, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %23 = "llvm.insertelement"(%22, %14, %4) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %24 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %25 = "llvm.insertelement"(%24, %14, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %26 = "llvm.insertelement"(%25, %11, %12) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %27 = "llvm.insertelement"(%26, %14, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %28 = "llvm.insertelement"(%27, %11, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %29 = "llvm.insertelement"(%28, %14, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %30 = "llvm.insertelement"(%29, %11, %6) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %31 = "llvm.insertelement"(%30, %14, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %32 = "llvm.insertelement"(%31, %11, %4) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %33 = "llvm.alloca"(%12) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %34 = "llvm.alloca"(%12) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %35 = "llvm.alloca"(%12) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %36 = "llvm.shufflevector"(%arg0, %13) <{mask = array<i32: 2, 0, 2, 1, 6, 4, 6, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %37 = "llvm.shufflevector"(%arg1, %13) <{mask = array<i32: 2, 0, 2, 1, 6, 4, 6, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %38 = "llvm.shufflevector"(%arg2, %13) <{mask = array<i32: 2, 0, 2, 1, 6, 4, 6, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %39 = "llvm.shufflevector"(%arg3, %13) <{mask = array<i32: 0, 2, 1, 2, 4, 6, 5, 6>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %40 = "llvm.shufflevector"(%arg4, %13) <{mask = array<i32: 0, 2, 1, 2, 4, 6, 5, 6>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %41 = "llvm.shufflevector"(%arg5, %13) <{mask = array<i32: 0, 2, 1, 2, 4, 6, 5, 6>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%33) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%34) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%35) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%33, %34, %35, %36, %37, %38, %39, %40, %41) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_quad_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
    %42 = "llvm.load"(%33) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %43 = "llvm.load"(%34) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %44 = "llvm.load"(%35) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%35) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%34) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%33) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %45 = "llvm.shufflevector"(%42, %43) <{mask = array<i32: 0, 8, 2, 10, 4, 12, 6, 14>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %46 = "llvm.shufflevector"(%42, %43) <{mask = array<i32: 1, 9, 3, 11, 5, 13, 7, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %47 = "llvm.shufflevector"(%44, %23) <{mask = array<i32: 0, 8, 2, 10, 4, 12, 6, 14>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %48 = "llvm.shufflevector"(%44, %32) <{mask = array<i32: 1, 9, 3, 11, 5, 13, 7, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %49 = "x86vector.avx512.intr.vpermi2var.q.512"(%45, %3, %47) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %50 = "x86vector.avx512.intr.vpermi2var.q.512"(%46, %3, %48) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %51 = "x86vector.avx512.intr.vpermi2var.q.512"(%45, %2, %47) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %52 = "x86vector.avx512.intr.vpermi2var.q.512"(%46, %2, %48) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %53 = "llvm.sub"(%50, %49) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %54 = "llvm.add"(%53, %1) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %55 = "llvm.call"(%54) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_is_nonzero, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> i32
    %56 = "llvm.xor"(%55, %0) : (i32, i32) -> i32
    %57 = "llvm.sub"(%52, %51) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %58 = "llvm.add"(%57, %1) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %59 = "llvm.call"(%58) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_is_nonzero, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> i32
    %60 = "llvm.xor"(%59, %12) : (i32, i32) -> i32
    %61 = "llvm.and"(%60, %56) : (i32, i32) -> i32
    "llvm.return"(%61) : (i32) -> ()
}
]

def fd_r43x6_ge_is_eq := [sllvm_of| fd_r43x6_ge_is_eq_region with
    @fd_r43x6_quad_mul_fast := fd_r43x6_quad_mul_fast_region,
     @fd_r43x6_is_nonzero := fd_r43x6_is_nonzero_region,
     @fd_long_if := fd_long_if_region]

end Firedancer.Avx512

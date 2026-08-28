/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Avx512.Mlir.fd_r43x6_quad_mul_fast
import SSA.Projects.Firedancer.Avx512.Mlir.fd_r43x6_is_nonzero

namespace Firedancer.Avx512
open LeanMLIR SLLVM

/-- `fd_r43x6_ge_is_eq`, as the compiler emits it: permute, one quad multiply
through the stack, unpack, two subtract-and-test-zeros. -/
def fd_r43x6_ge_is_eq_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: vector<8xi64>, %arg1: vector<8xi64>, %arg2: vector<8xi64>, %arg3: vector<8xi64>, %arg4: vector<8xi64>, %arg5: vector<8xi64>):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %2 = "llvm.mlir.poison"() : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %4 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %5 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %6 = "llvm.insertelement"(%4, %3, %5) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %7 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %8 = "llvm.insertelement"(%6, %2, %7) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %9 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %10 = "llvm.insertelement"(%8, %3, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %11 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %12 = "llvm.insertelement"(%10, %2, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %13 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %14 = "llvm.insertelement"(%12, %3, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %15 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %16 = "llvm.insertelement"(%14, %2, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %17 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %18 = "llvm.insertelement"(%16, %3, %17) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %19 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %20 = "llvm.insertelement"(%18, %2, %19) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %21 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %22 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %23 = "llvm.insertelement"(%21, %2, %22) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %24 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %25 = "llvm.insertelement"(%23, %3, %24) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %26 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %27 = "llvm.insertelement"(%25, %2, %26) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %28 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %29 = "llvm.insertelement"(%27, %3, %28) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %30 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %31 = "llvm.insertelement"(%29, %2, %30) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %32 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %33 = "llvm.insertelement"(%31, %3, %32) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %34 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %35 = "llvm.insertelement"(%33, %2, %34) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %36 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %37 = "llvm.insertelement"(%35, %3, %36) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %38 = "llvm.mlir.constant"() <{value = dense<[0, 1, 8, 4, 5, 12, 9, 9]> : vector<8xi64>}> : () -> vector<8xi64>
    %39 = "llvm.mlir.constant"() <{value = dense<[2, 3, 10, 6, 7, 14, 9, 9]> : vector<8xi64>}> : () -> vector<8xi64>
    %40 = "llvm.mlir.constant"() <{value = dense<[8796093022189, 8796093022207, 8796093022207, 8796093022207, 8796093022207, 1099511627775, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %41 = "llvm.mlir.constant"() <{value = -1 : i32}> : () -> i32
    %42 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %43 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %44 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %45 = "llvm.shufflevector"(%arg0, %1) <{mask = array<i32: 2, 0, 2, 1, 6, 4, 6, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %46 = "llvm.shufflevector"(%arg1, %1) <{mask = array<i32: 2, 0, 2, 1, 6, 4, 6, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %47 = "llvm.shufflevector"(%arg2, %1) <{mask = array<i32: 2, 0, 2, 1, 6, 4, 6, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %48 = "llvm.shufflevector"(%arg3, %1) <{mask = array<i32: 0, 2, 1, 2, 4, 6, 5, 6>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %49 = "llvm.shufflevector"(%arg4, %1) <{mask = array<i32: 0, 2, 1, 2, 4, 6, 5, 6>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %50 = "llvm.shufflevector"(%arg5, %1) <{mask = array<i32: 0, 2, 1, 2, 4, 6, 5, 6>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%42) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%43) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%44) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%42, %43, %44, %45, %46, %47, %48, %49, %50) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_quad_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
    %51 = "llvm.load"(%42) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %52 = "llvm.load"(%43) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %53 = "llvm.load"(%44) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%44) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%43) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%42) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %54 = "llvm.shufflevector"(%51, %52) <{mask = array<i32: 0, 8, 2, 10, 4, 12, 6, 14>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %55 = "llvm.shufflevector"(%51, %52) <{mask = array<i32: 1, 9, 3, 11, 5, 13, 7, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %56 = "llvm.shufflevector"(%53, %20) <{mask = array<i32: 0, 8, 2, 10, 4, 12, 6, 14>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %57 = "llvm.shufflevector"(%53, %37) <{mask = array<i32: 1, 9, 3, 11, 5, 13, 7, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %58 = "x86vector.avx512.intr.vpermi2var.q.512"(%54, %38, %56) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %59 = "x86vector.avx512.intr.vpermi2var.q.512"(%55, %38, %57) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %60 = "x86vector.avx512.intr.vpermi2var.q.512"(%54, %39, %56) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %61 = "x86vector.avx512.intr.vpermi2var.q.512"(%55, %39, %57) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %62 = "llvm.sub"(%59, %58) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %63 = "llvm.add"(%62, %40) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %64 = "llvm.call"(%63) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_is_nonzero, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> i32
    %65 = "llvm.xor"(%64, %41) : (i32, i32) -> i32
    %66 = "llvm.sub"(%61, %60) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %67 = "llvm.add"(%66, %40) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %68 = "llvm.call"(%67) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_is_nonzero, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> i32
    %69 = "llvm.xor"(%68, %0) : (i32, i32) -> i32
    %70 = "llvm.and"(%69, %65) : (i32, i32) -> i32
    "llvm.return"(%70) : (i32) -> ()
}
]

def fd_r43x6_ge_is_eq := [sllvm_of| fd_r43x6_ge_is_eq_region with
    @fd_r43x6_quad_mul_fast := fd_r43x6_quad_mul_fast_region,
     @fd_r43x6_is_nonzero := fd_r43x6_is_nonzero_region,
     @fd_long_if := fd_long_if_region]

end Firedancer.Avx512

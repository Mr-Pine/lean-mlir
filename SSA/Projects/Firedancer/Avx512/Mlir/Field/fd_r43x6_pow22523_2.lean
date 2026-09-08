/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_repsqr_mul2

/-!
# `fd_r43x6_pow22523_2` (avx512)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/avx512/region/fd_r43x6_pow22523_2.mlir`: two `x^((p-5)/8)` chains interleaved, over the `repsqr_mul2` ladder.

`fd_r43x6_repsqr_mul2` is bound by reference: it is a `Cfg`, and inlining
its region would ask a `Com` to hold three blocks.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_r43x6_pow22523_2_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: vector<8xi64>, %arg2: !llvm.ptr, %arg3: vector<8xi64>):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = dense<[8796093022207, 8796093022207, 8796093022207, 8796093022207, 8796093022207, 1099511627775, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %2 = "llvm.mlir.constant"() <{value = dense<[43, 43, 43, 43, 43, 40, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %3 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %4 = "llvm.mlir.constant"() <{value = dense<[19, 1, 1, 1, 1, 1, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %5 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 10 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 20 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 50 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 100 : i64}> : () -> i64
    %13 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %14 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %15 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %16 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %17 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %18 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %19 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %20 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %21 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %22 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %23 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %24 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %25 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %26 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %27 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %28 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %29 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %30 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %31 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %32 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %33 = "llvm.call"(%arg1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> vector<8xi64>
    %34 = "llvm.and"(%33, %1) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %35 = "llvm.lshr"(%33, %2) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %36 = "llvm.shufflevector"(%35, %3) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %37 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%34, %4, %36) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %38 = "llvm.call"(%arg3) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> vector<8xi64>
    %39 = "llvm.and"(%38, %1) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %40 = "llvm.lshr"(%38, %2) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %41 = "llvm.shufflevector"(%40, %3) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %42 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%39, %4, %41) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%13) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%14) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%13, %37, %arg1, %14, %42, %arg3, %5) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_repsqr_mul2, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, vector<8xi64>, vector<8xi64>, !llvm.ptr, vector<8xi64>, vector<8xi64>, i64) -> ()
    "llvm.intr.lifetime.start"(%15) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%16) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %43 = "llvm.load"(%13) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %44 = "llvm.load"(%14) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.call"(%15, %43, %37, %16, %44, %42, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_repsqr_mul2, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, vector<8xi64>, vector<8xi64>, !llvm.ptr, vector<8xi64>, vector<8xi64>, i64) -> ()
    "llvm.intr.lifetime.start"(%17) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%18) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %45 = "llvm.load"(%15) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %46 = "llvm.load"(%16) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.call"(%17, %45, %43, %18, %46, %44, %7) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_repsqr_mul2, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, vector<8xi64>, vector<8xi64>, !llvm.ptr, vector<8xi64>, vector<8xi64>, i64) -> ()
    "llvm.intr.lifetime.start"(%19) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%20) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %47 = "llvm.load"(%17) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %48 = "llvm.load"(%18) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.call"(%19, %47, %47, %20, %48, %48, %8) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_repsqr_mul2, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, vector<8xi64>, vector<8xi64>, !llvm.ptr, vector<8xi64>, vector<8xi64>, i64) -> ()
    "llvm.intr.lifetime.start"(%21) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%22) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %49 = "llvm.load"(%19) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %50 = "llvm.load"(%20) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.call"(%21, %49, %49, %22, %50, %50, %9) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_repsqr_mul2, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, vector<8xi64>, vector<8xi64>, !llvm.ptr, vector<8xi64>, vector<8xi64>, i64) -> ()
    "llvm.intr.lifetime.start"(%23) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%24) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %51 = "llvm.load"(%21) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %52 = "llvm.load"(%22) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.call"(%23, %51, %51, %24, %52, %52, %10) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_repsqr_mul2, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, vector<8xi64>, vector<8xi64>, !llvm.ptr, vector<8xi64>, vector<8xi64>, i64) -> ()
    "llvm.intr.lifetime.start"(%25) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%26) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %53 = "llvm.load"(%23) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %54 = "llvm.load"(%24) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.call"(%25, %53, %49, %26, %54, %50, %9) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_repsqr_mul2, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, vector<8xi64>, vector<8xi64>, !llvm.ptr, vector<8xi64>, vector<8xi64>, i64) -> ()
    "llvm.intr.lifetime.start"(%27) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%28) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %55 = "llvm.load"(%25) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %56 = "llvm.load"(%26) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.call"(%27, %55, %55, %28, %56, %56, %11) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_repsqr_mul2, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, vector<8xi64>, vector<8xi64>, !llvm.ptr, vector<8xi64>, vector<8xi64>, i64) -> ()
    "llvm.intr.lifetime.start"(%29) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%30) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %57 = "llvm.load"(%27) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %58 = "llvm.load"(%28) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.call"(%29, %57, %57, %30, %58, %58, %12) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_repsqr_mul2, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, vector<8xi64>, vector<8xi64>, !llvm.ptr, vector<8xi64>, vector<8xi64>, i64) -> ()
    "llvm.intr.lifetime.start"(%31) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%32) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %59 = "llvm.load"(%29) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %60 = "llvm.load"(%30) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.call"(%31, %59, %55, %32, %60, %56, %11) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_repsqr_mul2, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, vector<8xi64>, vector<8xi64>, !llvm.ptr, vector<8xi64>, vector<8xi64>, i64) -> ()
    %61 = "llvm.load"(%31) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %62 = "llvm.load"(%32) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.call"(%arg0, %61, %arg1, %arg2, %62, %arg3, %5) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_repsqr_mul2, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, vector<8xi64>, vector<8xi64>, !llvm.ptr, vector<8xi64>, vector<8xi64>, i64) -> ()
    "llvm.intr.lifetime.end"(%32) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%31) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%30) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%29) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%28) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%27) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%26) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%25) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%24) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%23) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%22) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%21) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%20) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%19) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%18) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%17) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%16) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%15) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%14) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%13) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

def fd_r43x6_pow22523_2 :
    Cfg (Ctxt.ofList [SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))), SLLVM.Ty.ptr, SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))), SLLVM.Ty.ptr]) [] :=
  [sllvm_cfg_of| fd_r43x6_pow22523_2_region with
    @fd_r43x6_repsqr_mul2 := fd_r43x6_repsqr_mul2,
    @fd_r43x6_sqr_fast := fd_r43x6_sqr_fast_cfg,
    @fd_r43x6_mul_fast := fd_r43x6_mul_fast_cfg]

end Firedancer.Avx512

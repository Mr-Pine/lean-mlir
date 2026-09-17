/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/avx512/region/fd_r43x6_repsqr_mul2.mlir
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_sqr_fast
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_mul_fast

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_r43x6_repsqr_mul2_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: vector<8xi64>, %arg2: vector<8xi64>, %arg3: !llvm.ptr, %arg4: vector<8xi64>, %arg5: vector<8xi64>, %arg6: i64):
    %0 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = dense<[19, 1, 1, 1, 1, 1, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %2 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = dense<[8796093022207, 8796093022207, 8796093022207, 8796093022207, 8796093022207, 1099511627775, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %4 = "llvm.mlir.constant"() <{value = dense<[43, 43, 43, 43, 43, 40, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %5 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %6 = "llvm.icmp"(%arg6, %2) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%6, %arg4, %arg1, %arg1, %arg4, %arg6)[^bb2, ^bb1] <{operandSegmentSizes = array<i32: 1, 2, 3>}> : (i1, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, i64) -> ()
  ^bb1(%7: vector<8xi64>, %8: vector<8xi64>, %9: i64):  // 2 preds: ^bb0, ^bb1
    %10 = "llvm.call"(%7) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> vector<8xi64>
    %11 = "llvm.and"(%10, %3) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %12 = "llvm.lshr"(%10, %4) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %13 = "llvm.shufflevector"(%12, %5) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %14 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%11, %1, %13) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %15 = "llvm.call"(%8) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> vector<8xi64>
    %16 = "llvm.and"(%15, %3) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %17 = "llvm.lshr"(%15, %4) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %18 = "llvm.shufflevector"(%17, %5) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %19 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%16, %1, %18) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %20 = "llvm.add"(%9, %0) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %21 = "llvm.icmp"(%20, %2) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%21, %19, %14, %14, %19, %20)[^bb2, ^bb1] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 2, 3>}> : (i1, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, i64) -> ()
  ^bb2(%22: vector<8xi64>, %23: vector<8xi64>):  // 2 preds: ^bb0, ^bb1
    %24 = "llvm.call"(%23, %arg2) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %25 = "llvm.and"(%24, %3) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %26 = "llvm.lshr"(%24, %4) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %27 = "llvm.shufflevector"(%26, %5) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %28 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%25, %1, %27) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %29 = "llvm.call"(%22, %arg5) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %30 = "llvm.and"(%29, %3) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %31 = "llvm.lshr"(%29, %4) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %32 = "llvm.shufflevector"(%31, %5) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %33 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%30, %1, %32) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%28, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%33, %arg3) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

sllvm_cfg_def fd_r43x6_repsqr_mul2 :
    Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 64, SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))), SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))), SLLVM.Ty.ptr, SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))), SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64))),
      SLLVM.Ty.ptr]) [] :=
  [sllvm_cfg_of| fd_r43x6_repsqr_mul2_region with
    @fd_r43x6_sqr_fast := fd_r43x6_sqr_fast_cfg,
    @fd_r43x6_mul_fast := fd_r43x6_mul_fast_cfg]

end Firedancer.Avx512

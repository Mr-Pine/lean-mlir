/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/avx512/region/fd_r43x6_diagnose.mlir
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Avx512.Mlir.Util.fd_int_if
import SSA.Projects.Firedancer.Avx512.Mlir.Util.fd_long_if

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_r43x6_diagnose_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: vector<8xi64>):
    %0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = -1048576 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 1099511627775 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 43 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 8796093022207 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 1048576 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 1099511627776 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %15 = "llvm.extractelement"(%arg0, %0) : (vector<8xi64>, i64) -> i64
    %16 = "llvm.extractelement"(%arg0, %1) : (vector<8xi64>, i64) -> i64
    %17 = "llvm.extractelement"(%arg0, %2) : (vector<8xi64>, i64) -> i64
    %18 = "llvm.extractelement"(%arg0, %3) : (vector<8xi64>, i64) -> i64
    %19 = "llvm.extractelement"(%arg0, %4) : (vector<8xi64>, i64) -> i64
    %20 = "llvm.extractelement"(%arg0, %5) : (vector<8xi64>, i64) -> i64
    %21 = "llvm.add"(%20, %6) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %22 = "llvm.ashr"(%21, %7) : (i64, i64) -> i64
    %23 = "llvm.and"(%21, %8) : (i64, i64) -> i64
    %24 = "llvm.mul"(%22, %9) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %25 = "llvm.add"(%24, %15) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %26 = "llvm.ashr"(%25, %10) : (i64, i64) -> i64
    %27 = "llvm.and"(%25, %11) : (i64, i64) -> i64
    %28 = "llvm.add"(%26, %16) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %29 = "llvm.ashr"(%28, %10) : (i64, i64) -> i64
    %30 = "llvm.and"(%28, %11) : (i64, i64) -> i64
    %31 = "llvm.add"(%29, %17) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %32 = "llvm.ashr"(%31, %10) : (i64, i64) -> i64
    %33 = "llvm.and"(%31, %11) : (i64, i64) -> i64
    %34 = "llvm.add"(%32, %18) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %35 = "llvm.ashr"(%34, %10) : (i64, i64) -> i64
    %36 = "llvm.and"(%34, %11) : (i64, i64) -> i64
    %37 = "llvm.add"(%35, %19) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %38 = "llvm.ashr"(%37, %10) : (i64, i64) -> i64
    %39 = "llvm.and"(%37, %11) : (i64, i64) -> i64
    %40 = "llvm.add"(%27, %9) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %41 = "llvm.lshr"(%40, %10) : (i64, i64) -> i64
    %42 = "llvm.and"(%40, %11) : (i64, i64) -> i64
    %43 = "llvm.add"(%30, %41) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %44 = "llvm.lshr"(%43, %10) : (i64, i64) -> i64
    %45 = "llvm.and"(%43, %11) : (i64, i64) -> i64
    %46 = "llvm.add"(%33, %44) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %47 = "llvm.lshr"(%46, %10) : (i64, i64) -> i64
    %48 = "llvm.and"(%46, %11) : (i64, i64) -> i64
    %49 = "llvm.add"(%36, %47) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %50 = "llvm.lshr"(%49, %10) : (i64, i64) -> i64
    %51 = "llvm.and"(%49, %11) : (i64, i64) -> i64
    %52 = "llvm.add"(%39, %50) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %53 = "llvm.lshr"(%52, %10) : (i64, i64) -> i64
    %54 = "llvm.and"(%52, %11) : (i64, i64) -> i64
    %55 = "llvm.add"(%23, %12) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %56 = "llvm.add"(%55, %38) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %57 = "llvm.add"(%56, %53) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %58 = "llvm.and"(%57, %8) : (i64, i64) -> i64
    %59 = "llvm.icmp"(%57, %13) <{predicate = 6 : i64}> : (i64, i64) -> i1
    %60 = "llvm.zext"(%59) : (i1) -> i32
    %61 = "llvm.call"(%60) <{CConv = #llvm.cconv<fastcc>, callee = @fd_long_if, fastmathFlags = #llvm.fastmath<none>}> : (i32) -> i64
    %62 = "llvm.sub"(%42, %61) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %63 = "llvm.ashr"(%62, %10) : (i64, i64) -> i64
    %64 = "llvm.add"(%63, %45) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %65 = "llvm.ashr"(%64, %10) : (i64, i64) -> i64
    %66 = "llvm.add"(%65, %48) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %67 = "llvm.ashr"(%66, %10) : (i64, i64) -> i64
    %68 = "llvm.add"(%67, %51) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %69 = "llvm.ashr"(%68, %10) : (i64, i64) -> i64
    %70 = "llvm.add"(%69, %54) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %71 = "llvm.ashr"(%70, %10) : (i64, i64) -> i64
    %72 = "llvm.add"(%71, %58) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %73 = "llvm.or"(%64, %62) : (i64, i64) -> i64
    %74 = "llvm.or"(%73, %66) : (i64, i64) -> i64
    %75 = "llvm.or"(%74, %68) : (i64, i64) -> i64
    %76 = "llvm.or"(%75, %70) : (i64, i64) -> i64
    %77 = "llvm.and"(%76, %11) : (i64, i64) -> i64
    %78 = "llvm.or"(%77, %72) : (i64, i64) -> i64
    %79 = "llvm.icmp"(%78, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
    %80 = "llvm.zext"(%79) : (i1) -> i32
    %81 = "llvm.trunc"(%62) : (i64) -> i32
    %82 = "llvm.and"(%81, %14) : (i32, i32) -> i32
    %83 = "llvm.call"(%80, %82) <{CConv = #llvm.cconv<fastcc>, callee = @fd_int_if, fastmathFlags = #llvm.fastmath<none>}> : (i32, i32) -> i32
    "llvm.return"(%83) : (i32) -> ()
}
]

def fd_r43x6_diagnose :=
  [sllvm_of| fd_r43x6_diagnose_region with
    @fd_int_if := fd_int_if_region,
    @fd_long_if := fd_long_if_region]

def fd_r43x6_diagnose_cfg := Cfg.ofCom (fd_r43x6_diagnose.castPureToEff .impure)

end Firedancer.Avx512

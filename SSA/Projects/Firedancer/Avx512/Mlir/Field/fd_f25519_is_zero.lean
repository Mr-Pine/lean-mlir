/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/avx512/region/fd_f25519_is_zero.mlir
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.SLLVM.Dialect

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_f25519_is_zero_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = dense<0> : vector<8xi64>}> : () -> vector<8xi64>
    %1 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %2 = "llvm.mlir.constant"() <{value = dense<[8796093022189, 8796093022207, 8796093022207, 8796093022207, 8796093022207, 1099511627775, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %3 = "llvm.mlir.constant"() <{value = true}> : () -> i1
    %4 = "llvm.load"(%arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %5 = "llvm.icmp"(%4, %0) <{predicate = 1 : i64}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi1>
    %6 = "llvm.bitcast"(%5) : (vector<8xi1>) -> i8
    %7 = "llvm.icmp"(%6, %1) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %8 = "llvm.icmp"(%4, %2) <{predicate = 1 : i64}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi1>
    %9 = "llvm.bitcast"(%8) : (vector<8xi1>) -> i8
    %10 = "llvm.icmp"(%9, %1) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %11 = "llvm.select"(%7, %3, %10) <{fastmathFlags = #llvm.fastmath<none>}> : (i1, i1, i1) -> i1
    %12 = "llvm.zext"(%11) : (i1) -> i32
    "llvm.return"(%12) : (i32) -> ()
}
]

def fd_f25519_is_zero : Cfg (Ctxt.ofList [SLLVM.Ty.ptr]) [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg_of| fd_f25519_is_zero_region]

end Firedancer.Avx512

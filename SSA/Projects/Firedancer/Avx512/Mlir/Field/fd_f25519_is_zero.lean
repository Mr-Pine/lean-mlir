/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.SLLVM.Dialect

/-!
# `fd_f25519_is_zero` (avx512)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/avx512/region/fd_f25519_is_zero.mlir`.

An exact *bit pattern* test, not a test on the represented value: the two
`wwl_eq`s compare against `fd_r43x6_zero()` and `fd_r43x6_p()`, so it answers
"is zero" only for a nearly reduced element with lanes 6 and 7 clear.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_f25519_is_zero_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = dense<0> : vector<8xi64>}> : () -> vector<8xi64>
    %2 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %3 = "llvm.mlir.constant"() <{value = dense<[8796093022189, 8796093022207, 8796093022207, 8796093022207, 8796093022207, 1099511627775, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %4 = "llvm.mlir.constant"() <{value = true}> : () -> i1
    %5 = "llvm.load"(%arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %6 = "llvm.icmp"(%5, %1) <{predicate = 1 : i64}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi1>
    %7 = "llvm.bitcast"(%6) : (vector<8xi1>) -> i8
    %8 = "llvm.icmp"(%7, %2) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %9 = "llvm.icmp"(%5, %3) <{predicate = 1 : i64}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi1>
    %10 = "llvm.bitcast"(%9) : (vector<8xi1>) -> i8
    %11 = "llvm.icmp"(%10, %2) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %12 = "llvm.select"(%8, %4, %11) <{fastmathFlags = #llvm.fastmath<none>}> : (i1, i1, i1) -> i1
    %13 = "llvm.zext"(%12) : (i1) -> i32
    "llvm.return"(%13) : (i32) -> ()
}
]

def fd_f25519_is_zero : Cfg (Ctxt.ofList [SLLVM.Ty.ptr]) [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg_of| fd_f25519_is_zero_region]

end Firedancer.Avx512

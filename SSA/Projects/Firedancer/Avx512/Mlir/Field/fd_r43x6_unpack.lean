/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# `fd_r43x6_unpack` (avx512)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/avx512/region/fd_r43x6_unpack.mlir`: the 32-byte little-endian scalar as six r43x6 limbs.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_r43x6_unpack_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: vector<4xi64>):
    %0 = "llvm.mlir.poison"() : () -> vector<4xi64>
    %1 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %3 = "llvm.mlir.poison"() : () -> vector<64xi8>
    %4 = "llvm.mlir.constant"() <{value = dense<[0, 3, 6, 1, 4, 7, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %5 = "llvm.mlir.constant"() <{value = dense<8796093022207> : vector<8xi64>}> : () -> vector<8xi64>
    %6 = "llvm.shufflevector"(%arg0, %0) <{mask = array<i32: 0, 1, 2, 3, -1, -1, -1, -1>}> : (vector<4xi64>, vector<4xi64>) -> vector<8xi64>
    %7 = "llvm.insertelement"(%6, %1, %2) : (vector<8xi64>, i64, i64) -> vector<8xi64>
    %8 = "llvm.bitcast"(%7) : (vector<8xi64>) -> vector<64xi8>
    %9 = "llvm.shufflevector"(%8, %3) <{mask = array<i32: 0, 1, 2, 3, 4, 5, 63, 63, 5, 6, 7, 8, 9, 10, 63, 63, 10, 11, 12, 13, 14, 15, 16, 63, 16, 17, 18, 19, 20, 21, 63, 63, 21, 22, 23, 24, 25, 26, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63>}> : (vector<64xi8>, vector<64xi8>) -> vector<64xi8>
    %10 = "llvm.bitcast"(%9) : (vector<64xi8>) -> vector<8xi64>
    %11 = "llvm.lshr"(%10, %4) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %12 = "llvm.and"(%11, %5) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.return"(%12) : (vector<8xi64>) -> ()
}
]

def fd_r43x6_unpack :=
  [sllvm_of| fd_r43x6_unpack_region]

end Firedancer.Avx512

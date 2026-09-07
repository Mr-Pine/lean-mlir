/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

namespace Firedancer.Avx512
open LeanMLIR SLLVM

/-- The region as an AST value, so it can be written once and used both as the
`Com` below and as the callee binding in `Mlir/fd_r43x6_is_nonzero.lean`. -/
def fd_long_if_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: i32):
    %0 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %3 = "llvm.icmp"(%arg0, %0) <{predicate = 0 : i64}> : (i32, i32) -> i1
    %4 = "llvm.select"(%3, %1, %2) <{fastmathFlags = #llvm.fastmath<none>}> : (i1, i64, i64) -> i64
    "llvm.return"(%4) : (i64) -> ()
}]

def fd_long_if := [sllvm_of| fd_long_if_region]

end Firedancer.Avx512

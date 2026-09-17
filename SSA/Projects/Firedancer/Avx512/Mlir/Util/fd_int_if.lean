/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/avx512/region/fd_int_if.mlir
module

public import SSA.Projects.SLLVM.Cfg
public import SSA.Projects.SLLVM.Dialect

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_int_if_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: i32, %arg1: i32):
    %0 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = -1 : i32}> : () -> i32
    %2 = "llvm.icmp"(%arg0, %0) <{predicate = 0 : i64}> : (i32, i32) -> i1
    %3 = "llvm.select"(%2, %arg1, %1) <{fastmathFlags = #llvm.fastmath<none>}> : (i1, i32, i32) -> i32
    "llvm.return"(%3) : (i32) -> ()
}
]

def fd_int_if :=
  [sllvm_of| fd_int_if_region]

def fd_int_if_cfg := Cfg.ofCom (fd_int_if.castPureToEff .impure)

end Firedancer.Avx512

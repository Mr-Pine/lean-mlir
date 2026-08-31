/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Ref.Mlir.fiat_25519_carry_square

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fd_f25519_sqr_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    "llvm.call"(%arg0, %arg1) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_carry_square, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

def fd_f25519_sqr : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_f25519_sqr_region with
    @fiat_25519_carry_square := fiat_25519_carry_square]

end Firedancer.Ref

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_add
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_carry

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fd_f25519_add_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr):
    "llvm.call"(%arg0, %arg1, %arg2) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_add, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.call"(%arg0, %arg0) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_carry, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

def fd_f25519_add : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_f25519_add_region with
    @fiat_25519_add := fiat_25519_add,
    @fiat_25519_carry := fiat_25519_carry]

end Firedancer.Ref

import SSA.Projects.SLLVM.Cfg

import SSA.Projects.Firedancer.Avx512.Mlir.fd_ed25519_point_eq

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_ed25519_point_eq_z1_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.call"(%arg0, %arg1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_eq, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> i32
    "llvm.return"(%0) : (i32) -> ()
}
]

def fd_ed25519_point_eq_z1 : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg_of| fd_ed25519_point_eq_z1_region with
    @fd_ed25519_point_eq := fd_ed25519_point_eq]

end Firedancer.Avx512

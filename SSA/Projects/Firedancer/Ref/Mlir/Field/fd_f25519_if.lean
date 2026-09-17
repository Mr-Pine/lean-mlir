-- build/native/gcc/mlir_canonicalized/ref/region/fd_f25519_if.mlir
module

public import SSA.Projects.SLLVM.Cfg
public import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_selectznz
-- callee bindings are evaluated while elaborating
public meta import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_selectznz

@[expose] public section

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fd_f25519_if_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: i32, %arg2: !llvm.ptr, %arg3: !llvm.ptr):
    %0 = "llvm.trunc"(%arg1) : (i32) -> i8
    "llvm.call"(%arg0, %0, %arg3, %arg2) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_selectznz, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, i8, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

sllvm_cfg_def fd_f25519_if : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 32, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_f25519_if_region with
    @fiat_25519_selectznz := fiat_25519_selectznz]

end Firedancer.Ref

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Ref.Mlir.fiat_25519_to_bytes

/-!
# `fd_f25519_tobytes` (ref)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/ref/region/fd_f25519_tobytes.mlir`. A thin wrapper around
`fiat_25519_to_bytes` that returns the out-parameter.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fd_f25519_tobytes_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    "llvm.call"(%arg0, %arg1) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_to_bytes, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

def fd_f25519_tobytes : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_f25519_tobytes_region with
    @fiat_25519_to_bytes := fiat_25519_to_bytes]

end Firedancer.Ref

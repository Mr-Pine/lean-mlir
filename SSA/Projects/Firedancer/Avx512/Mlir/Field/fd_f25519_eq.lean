/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_f25519_sub
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_f25519_is_zero

/-!
# `fd_f25519_eq` (avx512)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/avx512/region/fd_f25519_eq.mlir`. The same three lines
as the ref region -- a temporary, a `sub` into it, an `is_zero` on the result
-- over a 64-byte `fd_r43x6_t` rather than a 40-byte limb array.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_f25519_eq_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (vector<8xi64>)>>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%1) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %2 = "llvm.call"(%1, %arg0, %arg1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sub, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %3 = "llvm.call"(%1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_is_zero, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i32
    "llvm.intr.lifetime.end"(%1) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"(%3) : (i32) -> ()
}
]

def fd_f25519_eq : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg_of| fd_f25519_eq_region with
    @fd_f25519_sub := fd_f25519_sub,
    @fd_f25519_is_zero := fd_f25519_is_zero]

end Firedancer.Avx512

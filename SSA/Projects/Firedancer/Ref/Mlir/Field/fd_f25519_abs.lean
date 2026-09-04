/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_neg
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_sgn
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_if

/-!
Byte-identical (modulo indentation) to
`build/native/gcc/mlir/ref/region/fd_f25519_abs.mlir`. One 40-byte local holds
`-a`; `fd_f25519_if` selects it or `a` on `fd_f25519_sgn`'s bit.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fd_f25519_abs_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%1) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %2 = "llvm.call"(%1, %arg1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_neg, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %3 = "llvm.call"(%arg1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sgn, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i32
    %4 = "llvm.call"(%arg0, %3, %1, %arg1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_if, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, i32, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.end"(%1) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

def fd_f25519_abs : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_f25519_abs_region with
    @fd_f25519_neg := fd_f25519_neg,
    @fd_f25519_sgn := fd_f25519_sgn,
    @fd_f25519_if := fd_f25519_if]

end Firedancer.Ref

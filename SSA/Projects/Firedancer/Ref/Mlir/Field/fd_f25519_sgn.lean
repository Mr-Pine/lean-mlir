/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_tobytes

/-!
# `fd_f25519_sgn` (ref)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/ref/region/fd_f25519_sgn.mlir`. Serialises the field
element into a 32-byte stack buffer and returns its low bit, zero-extended.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fd_f25519_sgn_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %2 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<32 x i8>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%2) <{size = 32 : i64}> : (!llvm.ptr) -> ()
    %3 = "llvm.call"(%2, %arg0) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_tobytes, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %4 = "llvm.load"(%2) <{alignment = 16 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %5 = "llvm.and"(%4, %1) : (i8, i8) -> i8
    %6 = "llvm.zext"(%5) : (i8) -> i32
    "llvm.intr.lifetime.end"(%2) <{size = 32 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"(%6) : (i32) -> ()
}
]

def fd_f25519_sgn : Cfg (Ctxt.ofList [SLLVM.Ty.ptr]) [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg_of| fd_f25519_sgn_region with
    @fd_f25519_tobytes := fd_f25519_tobytes]

end Firedancer.Ref

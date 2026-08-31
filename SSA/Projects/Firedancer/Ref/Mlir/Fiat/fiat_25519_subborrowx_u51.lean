/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg

/-!
# `fiat_25519_subborrowx_u51` (ref)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/ref/region/fiat_25519_subborrowx_u51.mlir`. Subtracts a 51-bit limb and a borrow-in, storing the low 51 bits and the borrow-out through the two out-parameters.

The argument context is the block arguments reversed, as `Ctxt` orders them.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fiat_25519_subborrowx_u51_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: i8, %arg3: i64, %arg4: i64):
    %0 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %3 = "llvm.zext"(%arg2) : (i8) -> i64
    %4 = "llvm.add"(%3, %arg4) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %5 = "llvm.sub"(%arg3, %4) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %6 = "llvm.and"(%5, %0) : (i64, i64) -> i64
    "llvm.store"(%6, %arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %7 = "llvm.lshr"(%5, %1) : (i64, i64) -> i64
    %8 = "llvm.trunc"(%7) : (i64) -> i8
    %9 = "llvm.sub"(%2, %8) <{overflowFlags = #llvm.overflow<none>}> : (i8, i8) -> i8
    "llvm.store"(%9, %arg1) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

def fiat_25519_subborrowx_u51 :
    Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 8, SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [] :=
  [sllvm_cfg_of| fiat_25519_subborrowx_u51_region]

end Firedancer.Ref

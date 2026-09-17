/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/ref/region/fiat_25519_addcarryx_u51.mlir
import SSA.Projects.SLLVM.Cfg

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fiat_25519_addcarryx_u51_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: i8, %arg3: i64, %arg4: i64):
    %0 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %2 = "llvm.zext"(%arg2) : (i8) -> i64
    %3 = "llvm.add"(%2, %arg3) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %4 = "llvm.add"(%3, %arg4) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %5 = "llvm.and"(%4, %0) : (i64, i64) -> i64
    %6 = "llvm.lshr"(%4, %1) : (i64, i64) -> i64
    %7 = "llvm.trunc"(%6) : (i64) -> i8
    "llvm.store"(%5, %arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%7, %arg1) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

sllvm_cfg_def fiat_25519_addcarryx_u51 :
    Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 8, SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [] :=
  [sllvm_cfg_of| fiat_25519_addcarryx_u51_region]

end Firedancer.Ref

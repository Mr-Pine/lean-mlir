/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.SLLVM.Dialect

/-!
# `fd_f25519_sub` (avx512)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/avx512/region/fd_f25519_sub.mlir`:
`fd_r43x6_fold_signed( fd_r43x6_sub_fast( a, b ) )`.

`fold_signed` maps signed to *unreduced*, not to reduced -- the limbs it
returns are over-wide and not the canonical base-`2^43` digits. That is why
`fd_f25519_eq` needs reduced inputs; see `Conformance/Spec/fd_f25519_eq.lean`.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_f25519_sub_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = dense<[8795933638637, 8796091973631, 8796091973631, 8796091973631, 8796091973631, 1099510579199, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %1 = "llvm.mlir.constant"() <{value = dense<[8796093022207, 8796093022207, 8796093022207, 8796093022207, 8796093022207, 1099511627775, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %2 = "llvm.mlir.constant"() <{value = dense<[43, 43, 43, 43, 43, 40, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %3 = "llvm.mlir.constant"() <{value = dense<[5, 0, 1, 2, 3, 4, 8, 8]> : vector<8xi64>}> : () -> vector<8xi64>
    %4 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = dense<0> : vector<8xi64>}> : () -> vector<8xi64>
    %6 = "llvm.mlir.constant"() <{value = dense<18> : vector<8xi64>}> : () -> vector<8xi64>
    %7 = "llvm.mlir.constant"() <{value = dense<[-1, 0, 0, 0, 0, 0, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %8 = "llvm.mlir.constant"() <{value = dense<[159383552, 1048576, 1048576, 1048576, 1048576, 1048576, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %9 = "llvm.load"(%arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %10 = "llvm.load"(%arg2) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %11 = "llvm.sub"(%9, %10) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %12 = "llvm.add"(%11, %0) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %13 = "llvm.and"(%12, %1) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %14 = "llvm.ashr"(%12, %2) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %15 = "x86vector.avx512.intr.vpermi2var.q.512"(%14, %3, %5) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %16 = "llvm.mul"(%15, %6) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %17 = "llvm.and"(%16, %7) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %18 = "llvm.add"(%15, %8) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %19 = "llvm.add"(%18, %13) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %20 = "llvm.add"(%19, %17) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%20, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

def fd_f25519_sub : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_f25519_sub_region]

end Firedancer.Avx512

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/avx512/region/fd_ed25519_affine_is_small_order.mlir
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_to
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_f25519_is_zero
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_f25519_eq

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_ed25519_affine_is_small_order_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.addressof"() <{global_name = @fd_ed25519_order8_point_y0}> : () -> !llvm.ptr
    %2 = "llvm.mlir.addressof"() <{global_name = @fd_ed25519_order8_point_y1}> : () -> !llvm.ptr
    %3 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (vector<8xi64>)>>}> : (i32) -> !llvm.ptr
    %4 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (vector<8xi64>)>>}> : (i32) -> !llvm.ptr
    %5 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (vector<8xi64>)>>}> : (i32) -> !llvm.ptr
    %6 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (vector<8xi64>)>>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%3) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%4) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%5) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%6) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%3, %4, %5, %6, %arg0) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_to, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    %7 = "llvm.call"(%3) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_is_zero, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i32
    %8 = "llvm.call"(%4) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_is_zero, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i32
    %9 = "llvm.or"(%8, %7) : (i32, i32) -> i32
    %10 = "llvm.call"(%4, %1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_eq, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> i32
    %11 = "llvm.or"(%9, %10) : (i32, i32) -> i32
    %12 = "llvm.call"(%4, %2) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_eq, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> i32
    %13 = "llvm.or"(%11, %12) : (i32, i32) -> i32
    "llvm.intr.lifetime.end"(%6) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%5) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%4) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%3) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"(%13) : (i32) -> ()
}
]

sllvm_cfg_def fd_ed25519_affine_is_small_order :
    Cfg (Ctxt.ofList [SLLVM.Ty.ptr]) [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg_of| fd_ed25519_affine_is_small_order_region with
    @fd_ed25519_point_to := fd_ed25519_point_to,
    @fd_f25519_is_zero := fd_f25519_is_zero,
    @fd_f25519_eq := fd_f25519_eq]

end Firedancer.Avx512

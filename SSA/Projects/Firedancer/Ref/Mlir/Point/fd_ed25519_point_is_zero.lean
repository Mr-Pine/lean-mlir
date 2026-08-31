/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_is_zero
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_eq
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_sub
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_sub
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_carry

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fd_ed25519_point_is_zero_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %2 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %3 = "llvm.call"(%arg0) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_is_zero, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i32
    %4 = "llvm.getelementptr"(%arg0, %0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %5 = "llvm.getelementptr"(%arg0, %0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 3>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %6 = "llvm.call"(%4, %5) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_eq, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> i32
    %7 = "llvm.and"(%6, %3) : (i32, i32) -> i32
    "llvm.return"(%7) : (i32) -> ()
}
]

def fd_ed25519_point_is_zero : Cfg (Ctxt.ofList [SLLVM.Ty.ptr]) [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg_of| fd_ed25519_point_is_zero_region with
    @fd_f25519_is_zero := fd_f25519_is_zero_region,
    @fd_f25519_eq := fd_f25519_eq_region,
    @fd_f25519_sub := fd_f25519_sub_region,
    @fiat_25519_sub := fiat_25519_sub_region,
    @fiat_25519_carry := fiat_25519_carry_region]

end Firedancer.Ref

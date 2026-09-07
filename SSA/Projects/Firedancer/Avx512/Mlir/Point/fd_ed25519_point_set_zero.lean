import SSA.Projects.SLLVM.Cfg

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_ed25519_point_set_zero_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = dense<[0, 1, 1, 0, 0, 0, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %1 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %3 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %4 = "llvm.mlir.constant"() <{value = 128 : i64}> : () -> i64
    "llvm.store"(%0, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %5 = "llvm.getelementptr"(%arg0, %1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memset"(%5, %3, %4) <{isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

def fd_ed25519_point_set_zero : Cfg (Ctxt.ofList [SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_ed25519_point_set_zero_region]

end Firedancer.Avx512

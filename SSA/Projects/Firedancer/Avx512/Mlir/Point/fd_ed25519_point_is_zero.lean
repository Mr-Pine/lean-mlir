module

public import SSA.Projects.SLLVM.Cfg
public import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_set_zero
public import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_ge_is_eq
-- callee bindings are evaluated while elaborating
public meta import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_set_zero
public meta import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_ge_is_eq

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_ed25519_point_is_zero_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %3 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%3) <{size = 192 : i64}> : (!llvm.ptr) -> ()
    %4 = "llvm.call"(%3) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_set_zero, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> !llvm.ptr
    %5 = "llvm.load"(%arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %6 = "llvm.getelementptr"(%arg0, %1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %7 = "llvm.load"(%6) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %8 = "llvm.getelementptr"(%arg0, %1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 2>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %9 = "llvm.load"(%8) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %10 = "llvm.load"(%3) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %11 = "llvm.getelementptr"(%3, %1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %12 = "llvm.load"(%11) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %13 = "llvm.getelementptr"(%3, %1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 2>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %14 = "llvm.load"(%13) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %15 = "llvm.call"(%5, %7, %9, %10, %12, %14) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_ge_is_eq, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> i32
    "llvm.intr.lifetime.end"(%3) <{size = 192 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"(%15) : (i32) -> ()
}
]

sllvm_cfg_def fd_ed25519_point_is_zero : Cfg (Ctxt.ofList [SLLVM.Ty.ptr]) [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg_of| fd_ed25519_point_is_zero_region with
    @fd_ed25519_point_set_zero := fd_ed25519_point_set_zero,
    @fd_r43x6_ge_is_eq := fd_r43x6_ge_is_eq
  ]

end Firedancer.Avx512

-- build/native/gcc/mlir_canonicalized/ref/region/fd_f25519_sqrt_ratio.mlir
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_sqr
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_mul
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_eq
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_neg
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_if
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_abs
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_pow22523

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fd_f25519_sqrt_ratio_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.addressof"() <{global_name = @fd_f25519_sqrtm1}> : () -> !llvm.ptr
    %2 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %3 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %4 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %5 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %6 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %7 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %8 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %9 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %10 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %11 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%2) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %12 = "llvm.call"(%2, %arg2) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%3) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %13 = "llvm.call"(%3, %2, %arg2) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%4) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %14 = "llvm.call"(%4, %arg1, %3) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%5) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %15 = "llvm.call"(%5, %3) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%6) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %16 = "llvm.call"(%6, %5, %arg2) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%7) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %17 = "llvm.call"(%7, %arg1, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %18 = "llvm.call"(%arg0, %7) <{CConv = #llvm.cconv<ccc>, callee = @fd_f25519_pow22523, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %19 = "llvm.call"(%arg0, %arg0, %4) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%8) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %20 = "llvm.call"(%8, %arg0) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %21 = "llvm.call"(%8, %8, %arg2) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%9) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %22 = "llvm.call"(%9, %arg1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_neg, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%10) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %23 = "llvm.call"(%10, %9, %1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %24 = "llvm.call"(%8, %arg1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_eq, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> i32
    %25 = "llvm.call"(%8, %9) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_eq, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> i32
    %26 = "llvm.call"(%8, %10) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_eq, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> i32
    "llvm.intr.lifetime.start"(%11) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %27 = "llvm.call"(%11, %arg0, %1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %28 = "llvm.or"(%26, %25) : (i32, i32) -> i32
    %29 = "llvm.call"(%arg0, %28, %11, %arg0) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_if, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, i32, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %30 = "llvm.call"(%arg0, %arg0) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_abs, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %31 = "llvm.or"(%25, %24) : (i32, i32) -> i32
    "llvm.intr.lifetime.end"(%11) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%10) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%9) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%8) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%7) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%6) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%5) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%4) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%3) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%2) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"(%31) : (i32) -> ()
}
]

-- `@fd_f25519_sqrtm1` needs no binding: `llvm.mlir.addressof` reads its address
-- out of `GlobalState.globals`, and what lives there is a hypothesis of the
-- conformance theorem (`fd_f25519_sqrtm1_init` says what that is).
-- Returns `i32`, not a pointer: the artifact's `llvm.return` hands back the
-- `or` of the two `fd_f25519_eq` results, i.e. whether a root exists.
sllvm_cfg_def fd_f25519_sqrt_ratio :
    Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg_of| fd_f25519_sqrt_ratio_region with
    @fd_f25519_sqr := fd_f25519_sqr,
    @fd_f25519_mul := fd_f25519_mul,
    @fd_f25519_eq := fd_f25519_eq,
    @fd_f25519_neg := fd_f25519_neg,
    @fd_f25519_if := fd_f25519_if,
    @fd_f25519_abs := fd_f25519_abs,
    @fd_f25519_pow22523 := fd_f25519_pow22523]

end Firedancer.Ref

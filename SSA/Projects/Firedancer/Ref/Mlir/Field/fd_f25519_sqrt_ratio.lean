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
    %1 = "llvm.mlir.constant"() <{value = dense<[1718705420411056, 234908883556509, 2233514472574048, 2117202627021982, 765476049583133]> : tensor<5xi64>}> : () -> !llvm.array<5 x i64>
    %2 = "llvm.mlir.undef"() : () -> !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>
    %3 = "llvm.insertvalue"(%2, %1) <{position = array<i64: 0>}> : (!llvm.struct<"struct.fd_f25519", (array<5 x i64>)>, !llvm.array<5 x i64>) -> !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>
    %4 = "llvm.mlir.undef"() : () -> !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>
    %5 = "llvm.insertvalue"(%4, %3) <{position = array<i64: 0>}> : (!llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>) -> !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>
    %6 = "llvm.mlir.addressof"() <{global_name = @fd_f25519_sqrtm1}> : () -> !llvm.ptr
    %7 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %8 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %9 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %10 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %11 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %12 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %13 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %14 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %15 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %16 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%7) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %17 = "llvm.call"(%7, %arg2) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%8) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %18 = "llvm.call"(%8, %7, %arg2) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%9) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %19 = "llvm.call"(%9, %arg1, %8) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%10) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %20 = "llvm.call"(%10, %8) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%11) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %21 = "llvm.call"(%11, %10, %arg2) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%12) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %22 = "llvm.call"(%12, %arg1, %11) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %23 = "llvm.call"(%arg0, %12) <{CConv = #llvm.cconv<ccc>, callee = @fd_f25519_pow22523, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %24 = "llvm.call"(%arg0, %arg0, %9) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%13) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %25 = "llvm.call"(%13, %arg0) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_sqr, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %26 = "llvm.call"(%13, %13, %arg2) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%14) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %27 = "llvm.call"(%14, %arg1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_neg, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%15) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %28 = "llvm.call"(%15, %14, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %29 = "llvm.call"(%13, %arg1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_eq, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> i32
    %30 = "llvm.call"(%13, %14) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_eq, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> i32
    %31 = "llvm.call"(%13, %15) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_eq, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> i32
    "llvm.intr.lifetime.start"(%16) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    %32 = "llvm.call"(%16, %arg0, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_mul, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %33 = "llvm.or"(%31, %30) : (i32, i32) -> i32
    %34 = "llvm.call"(%arg0, %33, %16, %arg0) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_if, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, i32, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %35 = "llvm.call"(%arg0, %arg0) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_abs, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %36 = "llvm.or"(%30, %29) : (i32, i32) -> i32
    "llvm.intr.lifetime.end"(%16) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%15) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%14) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%13) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%12) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%11) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%10) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%9) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%8) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%7) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"(%36) : (i32) -> ()
}
]

-- `@fd_f25519_sqrtm1` needs no binding: `llvm.mlir.addressof` reads its address
-- out of `GlobalState.globals`, and what lives there is a hypothesis of the
-- conformance theorem (`fd_f25519_sqrtm1_init` says what that is).
-- Returns `i32`, not a pointer: the artifact's `llvm.return` hands back the
-- `or` of the two `fd_f25519_eq` results, i.e. whether a root exists.
def fd_f25519_sqrt_ratio :
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

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_to
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_f25519_is_zero
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_f25519_eq

/-!
# `fd_ed25519_affine_is_small_order` (AVX-512)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/avx512/region/fd_ed25519_affine_is_small_order.mlir`.

Same source as the ref region -- the shared `fd_curve25519.h` inline, not
`fd_r43x6_ge_is_small_order`, which is a different function this build never
reaches. The two regions agree op for op, differing only in

* the field representation (`vector<8xi64>` here, `!llvm.array<5 x i64>` there),
* alloca alignment (64 vs 16) and lifetime size (64 vs 40),
* the two constants `%1` and `%7`, which are the globals' initialisers in the
  respective encodings.

That is what makes the conformance proof a relational walk rather than two
independent specifications.

`%1`--`%5` and `%7`--`%11` are dead: they materialize the globals' initialisers
into SSA values that nothing consumes (`%5` and `%11` have no use). Only `%6`
and `%12`, the `addressof`es, reach the `fd_f25519_eq` calls; `addressof` needs
no `Cfg` binding, since it reads the symbol table out of the state.

This is the first AVX-512 region to use `llvm.insertvalue`, whose field here is
a `vector<8xi64>` rather than a flat `bitvec`. `SLLVMOp.insertvalue` carries the
field's `LLVM.Ty` and flattens through `LLVM.Ty.flatten` for exactly this case
(LIMITATIONS 7.3), so the region lifts verbatim -- no dead-code deletion.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_ed25519_affine_is_small_order_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = dense<[3034655877158, 7251661554934, 8531478563367, 3751701540842, 152657171260, 51416324880, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %2 = "llvm.mlir.undef"() : () -> !llvm.struct<"struct.fd_f25519", (vector<8xi64>)>
    %3 = "llvm.insertvalue"(%2, %1) <{position = array<i64: 0>}> : (!llvm.struct<"struct.fd_f25519", (vector<8xi64>)>, vector<8xi64>) -> !llvm.struct<"struct.fd_f25519", (vector<8xi64>)>
    %4 = "llvm.mlir.undef"() : () -> !llvm.array<1 x struct<"struct.fd_f25519", (vector<8xi64>)>>
    %5 = "llvm.insertvalue"(%4, %3) <{position = array<i64: 0>}> : (!llvm.array<1 x struct<"struct.fd_f25519", (vector<8xi64>)>>, !llvm.struct<"struct.fd_f25519", (vector<8xi64>)>) -> !llvm.array<1 x struct<"struct.fd_f25519", (vector<8xi64>)>>
    %6 = "llvm.mlir.addressof"() <{global_name = @fd_ed25519_order8_point_y0}> : () -> !llvm.ptr
    %7 = "llvm.mlir.constant"() <{value = dense<[5761437145031, 1544431467273, 264614458840, 5044391481365, 8643435850947, 1048095302895, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %8 = "llvm.mlir.undef"() : () -> !llvm.struct<"struct.fd_f25519", (vector<8xi64>)>
    %9 = "llvm.insertvalue"(%8, %7) <{position = array<i64: 0>}> : (!llvm.struct<"struct.fd_f25519", (vector<8xi64>)>, vector<8xi64>) -> !llvm.struct<"struct.fd_f25519", (vector<8xi64>)>
    %10 = "llvm.mlir.undef"() : () -> !llvm.array<1 x struct<"struct.fd_f25519", (vector<8xi64>)>>
    %11 = "llvm.insertvalue"(%10, %9) <{position = array<i64: 0>}> : (!llvm.array<1 x struct<"struct.fd_f25519", (vector<8xi64>)>>, !llvm.struct<"struct.fd_f25519", (vector<8xi64>)>) -> !llvm.array<1 x struct<"struct.fd_f25519", (vector<8xi64>)>>
    %12 = "llvm.mlir.addressof"() <{global_name = @fd_ed25519_order8_point_y1}> : () -> !llvm.ptr
    %13 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (vector<8xi64>)>>}> : (i32) -> !llvm.ptr
    %14 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (vector<8xi64>)>>}> : (i32) -> !llvm.ptr
    %15 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (vector<8xi64>)>>}> : (i32) -> !llvm.ptr
    %16 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (vector<8xi64>)>>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%13) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%14) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%15) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%16) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%13, %14, %15, %16, %arg0) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_to, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    %17 = "llvm.call"(%13) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_is_zero, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i32
    %18 = "llvm.call"(%14) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_is_zero, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i32
    %19 = "llvm.or"(%18, %17) : (i32, i32) -> i32
    %20 = "llvm.call"(%14, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_eq, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> i32
    %21 = "llvm.or"(%19, %20) : (i32, i32) -> i32
    %22 = "llvm.call"(%14, %12) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_eq, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> i32
    %23 = "llvm.or"(%21, %22) : (i32, i32) -> i32
    "llvm.intr.lifetime.end"(%16) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%15) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%14) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%13) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"(%23) : (i32) -> ()
}
]

def fd_ed25519_affine_is_small_order :
    Cfg (Ctxt.ofList [SLLVM.Ty.ptr]) [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg_of| fd_ed25519_affine_is_small_order_region with
    @fd_ed25519_point_to := fd_ed25519_point_to,
    @fd_f25519_is_zero := fd_f25519_is_zero,
    @fd_f25519_eq := fd_f25519_eq]

end Firedancer.Avx512

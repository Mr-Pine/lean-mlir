/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_to
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_is_zero
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_eq

/-!
# `fd_ed25519_affine_is_small_order` (ref)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/ref/region/fd_ed25519_affine_is_small_order.mlir`.

The shared `fd_curve25519.h` inline: copy the point out with
`fd_ed25519_point_to`, then `X == 0 | Y == 0 | Y == y0 | Y == y1`. The AVX-512
build compiles the *same* source, so its region differs only in the field
representation -- see the note in the conformance spec.

`%1`--`%5` and `%7`--`%11` are dead: they materialize the two globals'
initializers into SSA values that nothing consumes. Only `%6` and `%12`, the
`addressof`es, reach the `fd_f25519_eq` calls. `addressof` needs no binding --
it reads the symbol table out of the state.

`%15` and `%16` (`z`, `t`) are written by `fd_ed25519_point_to` and never read
back; only `%13` (`x`) and `%14` (`y`) are.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fd_ed25519_affine_is_small_order_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = dense<[2166873539340326, 1778179147085316, 1886209374839743, 1223329526802818, 105300633354275]> : tensor<5xi64>}> : () -> !llvm.array<5 x i64>
    %2 = "llvm.mlir.undef"() : () -> !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>
    %3 = "llvm.insertvalue"(%2, %1) <{position = array<i64: 0>}> : (!llvm.struct<"struct.fd_f25519", (array<5 x i64>)>, !llvm.array<5 x i64>) -> !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>
    %4 = "llvm.mlir.undef"() : () -> !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>
    %5 = "llvm.insertvalue"(%4, %3) <{position = array<i64: 0>}> : (!llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>) -> !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>
    %6 = "llvm.mlir.addressof"() <{global_name = @fd_ed25519_order8_point_y0}> : () -> !llvm.ptr
    %7 = "llvm.mlir.constant"() <{value = dense<[84926274344903, 473620666599931, 365590438845504, 1028470286882429, 2146499180330972]> : tensor<5xi64>}> : () -> !llvm.array<5 x i64>
    %8 = "llvm.mlir.undef"() : () -> !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>
    %9 = "llvm.insertvalue"(%8, %7) <{position = array<i64: 0>}> : (!llvm.struct<"struct.fd_f25519", (array<5 x i64>)>, !llvm.array<5 x i64>) -> !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>
    %10 = "llvm.mlir.undef"() : () -> !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>
    %11 = "llvm.insertvalue"(%10, %9) <{position = array<i64: 0>}> : (!llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>) -> !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>
    %12 = "llvm.mlir.addressof"() <{global_name = @fd_ed25519_order8_point_y1}> : () -> !llvm.ptr
    %13 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %14 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %15 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %16 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%13) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%14) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%15) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%16) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%13, %14, %15, %16, %arg0) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ed25519_point_to, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    %17 = "llvm.call"(%13) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_is_zero, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i32
    %18 = "llvm.call"(%14) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_is_zero, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr) -> i32
    %19 = "llvm.or"(%18, %17) : (i32, i32) -> i32
    %20 = "llvm.call"(%14, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_eq, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> i32
    %21 = "llvm.or"(%19, %20) : (i32, i32) -> i32
    %22 = "llvm.call"(%14, %12) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_eq, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> i32
    %23 = "llvm.or"(%21, %22) : (i32, i32) -> i32
    "llvm.intr.lifetime.end"(%16) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%15) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%14) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%13) <{size = 40 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"(%23) : (i32) -> ()
}
]

def fd_ed25519_affine_is_small_order :
    Cfg (Ctxt.ofList [SLLVM.Ty.ptr]) [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg_of| fd_ed25519_affine_is_small_order_region with
    @fd_ed25519_point_to := fd_ed25519_point_to,
    @fd_f25519_is_zero := fd_f25519_is_zero,
    @fd_f25519_eq := fd_f25519_eq]

end Firedancer.Ref

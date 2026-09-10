/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_r43x6_ge_decode2

/-!
# `fd_ed25519_point_frombytes_2x` (avx512)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/avx512/region/fd_ed25519_point_frombytes_2x.mlir`:
`FD_R43X6_GE_DECODE2( r1->P, buf1, r2->P, buf2 )`, macro-expanded.

The macro decodes into six `wwl_t` locals and then copies them into the two
`FD_R43X6_QUAD`s, so the region is one call plus six load/store pairs. Unlike
the `ref` layer there is no short-circuit here: the callee returns `0`, `-1`
or `-2` and the region passes it through.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_ed25519_point_frombytes_2x_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr, %arg3: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %3 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %4 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %5 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %6 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %7 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %8 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%3) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%4) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%5) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%6) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%7) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%8) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %9 = "llvm.call"(%3, %4, %5, %arg1, %6, %7, %8, %arg3) <{CConv = #llvm.cconv<ccc>, callee = @fd_r43x6_ge_decode2, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr) -> i32
    %10 = "llvm.load"(%3) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.store"(%10, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %11 = "llvm.load"(%4) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %12 = "llvm.getelementptr"(%arg0, %1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%11, %12) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %13 = "llvm.load"(%5) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %14 = "llvm.getelementptr"(%arg0, %1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 2>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%13, %14) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %15 = "llvm.load"(%6) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.store"(%15, %arg2) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %16 = "llvm.load"(%7) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %17 = "llvm.getelementptr"(%arg2, %1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%16, %17) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %18 = "llvm.load"(%8) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %19 = "llvm.getelementptr"(%arg2, %1) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 2>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%18, %19) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%8) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%7) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%6) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%5) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%4) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%3) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"(%9) : (i32) -> ()
}
]

set_option maxHeartbeats 1000000 in
def fd_ed25519_point_frombytes_2x :
    Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr])
      [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg_of| fd_ed25519_point_frombytes_2x_region with
    @fd_r43x6_ge_decode2 := fd_r43x6_ge_decode2]

end Firedancer.Avx512

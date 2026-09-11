/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_memset
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_sha512_core_ref
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_ulong_bswap

/-!
# `fd_sha512_fini` (common)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/{ref,avx512}/region/fd_sha512_fini.mlir`. The two
backends emit the same file, so the function is lifted once, here.

`fd_sha512.c`: pad, append the length, compress, and byte-swap the eight
state words into `hash`. Returns `hash` (`%arg1`).
-/

namespace Firedancer.Common
open LeanMLIR SLLVM

set_option maxRecDepth 100000 in
def fd_sha512_fini_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %2 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %3 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %4 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %5 = "llvm.mlir.constant"() <{value = -128 : i8}> : () -> i8
    %6 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 112 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 127 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %10 = "llvm.mlir.constant"() <{value = 120 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %15 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %16 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %17 = "llvm.getelementptr"(%arg0, %0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %18 = "llvm.getelementptr"(%arg0, %0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 3>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %19 = "llvm.load"(%18) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (!llvm.ptr) -> i64
    %20 = "llvm.getelementptr"(%arg0, %0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 4>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %21 = "llvm.load"(%20) <{alignment = 16 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag3]}> : (!llvm.ptr) -> i64
    %22 = "llvm.getelementptr"(%arg0, %0) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 5>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %23 = "llvm.load"(%22) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag4]}> : (!llvm.ptr) -> i64
    %24 = "llvm.getelementptr"(%arg0, %19) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%5, %24) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i8, !llvm.ptr) -> ()
    %25 = "llvm.add"(%19, %6) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %26 = "llvm.icmp"(%25, %7) <{predicate = 8 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%26, %25)[^bb1, ^bb2] <{branch_weights = array<i32: 1, 2000>, operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i64) -> ()
  ^bb1:  // pred: ^bb0
    %27 = "llvm.getelementptr"(%arg0, %25) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %28 = "llvm.sub"(%8, %19) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %29 = "llvm.call"(%27, %28) <{CConv = #llvm.cconv<fastcc>, callee = @fd_memset, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.call"(%17, %arg0, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_sha512_core_ref, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.br"(%0)[^bb2] : (i64) -> ()
  ^bb2(%30: i64):  // 2 preds: ^bb0, ^bb1
    %31 = "llvm.getelementptr"(%arg0, %30) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %32 = "llvm.sub"(%7, %30) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %33 = "llvm.call"(%31, %32) <{CConv = #llvm.cconv<fastcc>, callee = @fd_memset, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %34 = "llvm.call"(%23) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_bswap, fastmathFlags = #llvm.fastmath<none>}> : (i64) -> i64
    %35 = "llvm.getelementptr"(%arg0, %0, %7) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 0, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    "llvm.store"(%34, %35) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %36 = "llvm.call"(%21) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_bswap, fastmathFlags = #llvm.fastmath<none>}> : (i64) -> i64
    %37 = "llvm.getelementptr"(%arg0, %0, %10) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 0, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    "llvm.store"(%36, %37) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    "llvm.call"(%17, %arg0, %6) <{CConv = #llvm.cconv<fastcc>, callee = @fd_sha512_core_ref, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %38 = "llvm.load"(%17) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %39 = "llvm.call"(%38) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_bswap, fastmathFlags = #llvm.fastmath<none>}> : (i64) -> i64
    "llvm.store"(%39, %arg1) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %40 = "llvm.getelementptr"(%arg0, %0, %6) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    %41 = "llvm.load"(%40) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %42 = "llvm.call"(%41) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_bswap, fastmathFlags = #llvm.fastmath<none>}> : (i64) -> i64
    %43 = "llvm.getelementptr"(%arg1, %6) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%42, %43) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %44 = "llvm.getelementptr"(%arg0, %0, %11) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    %45 = "llvm.load"(%44) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %46 = "llvm.call"(%45) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_bswap, fastmathFlags = #llvm.fastmath<none>}> : (i64) -> i64
    %47 = "llvm.getelementptr"(%arg1, %11) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%46, %47) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %48 = "llvm.getelementptr"(%arg0, %0, %12) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    %49 = "llvm.load"(%48) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %50 = "llvm.call"(%49) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_bswap, fastmathFlags = #llvm.fastmath<none>}> : (i64) -> i64
    %51 = "llvm.getelementptr"(%arg1, %12) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%50, %51) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %52 = "llvm.getelementptr"(%arg0, %0, %13) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    %53 = "llvm.load"(%52) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %54 = "llvm.call"(%53) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_bswap, fastmathFlags = #llvm.fastmath<none>}> : (i64) -> i64
    %55 = "llvm.getelementptr"(%arg1, %13) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%54, %55) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %56 = "llvm.getelementptr"(%arg0, %0, %14) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    %57 = "llvm.load"(%56) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %58 = "llvm.call"(%57) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_bswap, fastmathFlags = #llvm.fastmath<none>}> : (i64) -> i64
    %59 = "llvm.getelementptr"(%arg1, %14) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%58, %59) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %60 = "llvm.getelementptr"(%arg0, %0, %15) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    %61 = "llvm.load"(%60) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %62 = "llvm.call"(%61) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_bswap, fastmathFlags = #llvm.fastmath<none>}> : (i64) -> i64
    %63 = "llvm.getelementptr"(%arg1, %15) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%62, %63) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %64 = "llvm.getelementptr"(%arg0, %0, %16) <{elem_type = !llvm.struct<"struct.fd_sha512_private", (array<128 x i8>, array<8 x i64>, i64, i64, i64, i64, array<32 x i8>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    %65 = "llvm.load"(%64) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %66 = "llvm.call"(%65) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_bswap, fastmathFlags = #llvm.fastmath<none>}> : (i64) -> i64
    %67 = "llvm.getelementptr"(%arg1, %16) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%66, %67) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    "llvm.return"(%arg1) : (!llvm.ptr) -> ()
}
]

set_option maxRecDepth 100000 in
def fd_sha512_fini : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_sha512_fini_region with
    @fd_memset := fd_memset,
    @fd_sha512_core_ref := fd_sha512_core_ref,
    @fd_ulong_bswap := fd_ulong_bswap]

end Firedancer.Common

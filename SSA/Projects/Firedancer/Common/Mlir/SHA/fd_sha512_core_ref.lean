/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_ulong_bswap
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_ulong_rotate_right

/-!
# `fd_sha512_core_ref` (common)

Byte-identical (modulo indentation) to
`build/native/gcc/mlir/{ref,avx512}/region/fd_sha512_core_ref.mlir`. The two
backends emit the same file, so the function is lifted once, here.

`fd_sha512.c`: the block compression function, `block_cnt` blocks at a
time. Three loops -- the 16-word load, the 80-round message schedule and
the compression proper -- so `^bb1`, `^bb2` and `^bb3` all carry back-edges,
with nine and ten block arguments respectively. The round constants reach it
as the global `@fd_sha512_core_ref.K`.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM

set_option maxRecDepth 100000 in
def fd_sha512_core_ref_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: i64):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 14 : i32}> : () -> i32
    %10 = "llvm.mlir.constant"() <{value = 18 : i32}> : () -> i32
    %11 = "llvm.mlir.constant"() <{value = 41 : i32}> : () -> i32
    %12 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = dense<[4794697086780616226, 8158064640168781261, -5349999486874862801, -1606136188198331460, 4131703408338449720, 6480981068601479193, -7908458776815382629, -6116909921290321640, -2880145864133508542, 1334009975649890238, 2608012711638119052, 6128411473006802146, 8268148722764581231, -9160688886553864527, -7215885187991268811, -4495734319001033068, -1973867731355612462, -1171420211273849373, 1135362057144423861, 2597628984639134821, 3308224258029322869, 5365058923640841347, 6679025012923562964, 8573033837759648693, -7476448914759557205, -6327057829258317296, -5763719355590565569, -4658551843659510044, -4116276920077217854, -3051310485924567259, 489312712824947311, 1452737877330783856, 2861767655752347644, 3322285676063803686, 5560940570517711597, 5996557281743188959, 7280758554555802590, 8532644243296465576, -9096487096722542874, -7894198246740708037, -6719396339535248540, -6333637450476146687, -4446306890439682159, -4076793802049405392, -3345356375505022440, -2983346525034927856, -860691631967231958, 1182934255886127544, 1847814050463011016, 2177327727835720531, 2830643537854262169, 3796741975233480872, 4115178125766777443, 5681478168544905931, 6601373596472566643, 7507060721942968483, 8399075790359081724, 8693463985226723168, -8878714635349349518, -8302665154208450068, -8016688836872298968, -6606660893046293015, -4685533653050689259, -4147400797238176981, -3880063495543823972, -3348786107499101689, -1523767162380948706, -757361751448694408, 500013540394364858, 748580250866718886, 1242879168328830382, 1977374033974150939, 2944078676154940804, 3659926193048069267, 4368137639120453308, 4836135668995329356, 5532061633213252278, 6448918945643986474, 6902733635092675308, 7801388544844847127]> : tensor<80xi64>}> : () -> !llvm.array<80 x i64>
    %14 = "llvm.mlir.addressof"() <{global_name = @fd_sha512_core_ref.K}> : () -> !llvm.ptr
    %15 = "llvm.mlir.constant"() <{value = 28 : i32}> : () -> i32
    %16 = "llvm.mlir.constant"() <{value = 34 : i32}> : () -> i32
    %17 = "llvm.mlir.constant"() <{value = 39 : i32}> : () -> i32
    %18 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %19 = "llvm.mlir.constant"() <{value = 15 : i64}> : () -> i64
    %20 = "llvm.mlir.constant"() <{value = 14 : i64}> : () -> i64
    %21 = "llvm.mlir.constant"() <{value = 8 : i32}> : () -> i32
    %22 = "llvm.mlir.constant"() <{value = 19 : i32}> : () -> i32
    %23 = "llvm.mlir.constant"() <{value = 61 : i32}> : () -> i32
    %24 = "llvm.mlir.constant"() <{value = 9 : i64}> : () -> i64
    %25 = "llvm.mlir.constant"() <{value = 80 : i64}> : () -> i64
    %26 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<16 x i64>}> : (i32) -> !llvm.ptr
    %27 = "llvm.getelementptr"(%arg0, %1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %28 = "llvm.getelementptr"(%arg0, %2) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %29 = "llvm.getelementptr"(%arg0, %3) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %30 = "llvm.getelementptr"(%arg0, %4) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %31 = "llvm.getelementptr"(%arg0, %5) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %32 = "llvm.getelementptr"(%arg0, %6) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %33 = "llvm.getelementptr"(%arg0, %7) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %34 = "llvm.load"(%arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %35 = "llvm.load"(%27) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %36 = "llvm.load"(%28) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %37 = "llvm.load"(%29) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %38 = "llvm.load"(%30) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %39 = "llvm.load"(%31) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %40 = "llvm.load"(%32) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %41 = "llvm.load"(%33) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.br"(%41, %40, %39, %38, %37, %36, %35, %34, %arg1, %arg2)[^bb1] : (i64, i64, i64, i64, i64, i64, i64, i64, !llvm.ptr, i64) -> ()
  ^bb1(%42: i64, %43: i64, %44: i64, %45: i64, %46: i64, %47: i64, %48: i64, %49: i64, %50: !llvm.ptr, %51: i64):  // 2 preds: ^bb0, ^bb4
    "llvm.intr.lifetime.start"(%26) <{size = 128 : i64}> : (!llvm.ptr) -> ()
    "llvm.br"(%49, %48, %47, %46, %8, %42, %43, %44, %45)[^bb2] : (i64, i64, i64, i64, i64, i64, i64, i64, i64) -> ()
  ^bb2(%52: i64, %53: i64, %54: i64, %55: i64, %56: i64, %57: i64, %58: i64, %59: i64, %60: i64):  // 2 preds: ^bb1, ^bb2
    %61 = "llvm.getelementptr"(%50, %56) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %62 = "llvm.load"(%61) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %63 = "llvm.call"(%62) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_bswap, fastmathFlags = #llvm.fastmath<none>}> : (i64) -> i64
    %64 = "llvm.getelementptr"(%26, %8, %56) <{elem_type = !llvm.array<16 x i64>, inbounds, rawConstantIndices = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    "llvm.store"(%63, %64) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %65 = "llvm.call"(%60, %9) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %66 = "llvm.call"(%60, %10) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %67 = "llvm.xor"(%66, %65) : (i64, i64) -> i64
    %68 = "llvm.call"(%60, %11) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %69 = "llvm.xor"(%67, %68) : (i64, i64) -> i64
    %70 = "llvm.and"(%59, %60) : (i64, i64) -> i64
    %71 = "llvm.xor"(%60, %12) : (i64, i64) -> i64
    %72 = "llvm.and"(%58, %71) : (i64, i64) -> i64
    %73 = "llvm.getelementptr"(%14, %8, %56) <{elem_type = !llvm.array<80 x i64>, inbounds, rawConstantIndices = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    %74 = "llvm.load"(%73) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %75 = "llvm.or"(%72, %70) : (i64, i64) -> i64
    %76 = "llvm.add"(%75, %57) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %77 = "llvm.add"(%76, %63) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %78 = "llvm.add"(%77, %69) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %79 = "llvm.add"(%78, %74) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %80 = "llvm.call"(%52, %15) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %81 = "llvm.call"(%52, %16) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %82 = "llvm.xor"(%81, %80) : (i64, i64) -> i64
    %83 = "llvm.call"(%52, %17) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %84 = "llvm.xor"(%82, %83) : (i64, i64) -> i64
    %85 = "llvm.xor"(%53, %54) : (i64, i64) -> i64
    %86 = "llvm.and"(%52, %85) : (i64, i64) -> i64
    %87 = "llvm.and"(%53, %54) : (i64, i64) -> i64
    %88 = "llvm.xor"(%86, %87) : (i64, i64) -> i64
    %89 = "llvm.add"(%79, %55) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %90 = "llvm.add"(%79, %88) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %91 = "llvm.add"(%90, %84) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %92 = "llvm.add"(%56, %1) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %93 = "llvm.icmp"(%92, %18) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%93, %91, %52, %53, %54, %18, %58, %59, %60, %89, %91, %52, %53, %54, %92, %58, %59, %60, %89)[^bb3, ^bb2] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 9, 9>}> : (i1, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64) -> ()
  ^bb3(%94: i64, %95: i64, %96: i64, %97: i64, %98: i64, %99: i64, %100: i64, %101: i64, %102: i64):  // 2 preds: ^bb2, ^bb3
    %103 = "llvm.add"(%98, %1) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %104 = "llvm.and"(%103, %19) : (i64, i64) -> i64
    %105 = "llvm.getelementptr"(%26, %8, %104) <{elem_type = !llvm.array<16 x i64>, inbounds, rawConstantIndices = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    %106 = "llvm.load"(%105) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %107 = "llvm.add"(%98, %20) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %108 = "llvm.and"(%107, %19) : (i64, i64) -> i64
    %109 = "llvm.getelementptr"(%26, %8, %108) <{elem_type = !llvm.array<16 x i64>, inbounds, rawConstantIndices = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    %110 = "llvm.load"(%109) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %111 = "llvm.call"(%106, %0) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %112 = "llvm.call"(%106, %21) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %113 = "llvm.lshr"(%106, %7) : (i64, i64) -> i64
    %114 = "llvm.xor"(%111, %113) : (i64, i64) -> i64
    %115 = "llvm.xor"(%114, %112) : (i64, i64) -> i64
    %116 = "llvm.call"(%110, %22) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %117 = "llvm.call"(%110, %23) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %118 = "llvm.lshr"(%110, %6) : (i64, i64) -> i64
    %119 = "llvm.xor"(%116, %118) : (i64, i64) -> i64
    %120 = "llvm.xor"(%119, %117) : (i64, i64) -> i64
    %121 = "llvm.add"(%98, %24) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %122 = "llvm.and"(%121, %19) : (i64, i64) -> i64
    %123 = "llvm.getelementptr"(%26, %8, %122) <{elem_type = !llvm.array<16 x i64>, inbounds, rawConstantIndices = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    %124 = "llvm.load"(%123) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %125 = "llvm.and"(%98, %19) : (i64, i64) -> i64
    %126 = "llvm.getelementptr"(%26, %8, %125) <{elem_type = !llvm.array<16 x i64>, inbounds, rawConstantIndices = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    %127 = "llvm.load"(%126) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %128 = "llvm.add"(%124, %115) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %129 = "llvm.add"(%128, %120) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %130 = "llvm.add"(%129, %127) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.store"(%130, %126) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %131 = "llvm.call"(%102, %9) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %132 = "llvm.call"(%102, %10) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %133 = "llvm.xor"(%132, %131) : (i64, i64) -> i64
    %134 = "llvm.call"(%102, %11) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %135 = "llvm.xor"(%133, %134) : (i64, i64) -> i64
    %136 = "llvm.and"(%101, %102) : (i64, i64) -> i64
    %137 = "llvm.xor"(%102, %12) : (i64, i64) -> i64
    %138 = "llvm.and"(%100, %137) : (i64, i64) -> i64
    %139 = "llvm.getelementptr"(%14, %8, %98) <{elem_type = !llvm.array<80 x i64>, inbounds, rawConstantIndices = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    %140 = "llvm.load"(%139) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %141 = "llvm.or"(%138, %136) : (i64, i64) -> i64
    %142 = "llvm.add"(%141, %99) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %143 = "llvm.add"(%142, %130) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %144 = "llvm.add"(%143, %135) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %145 = "llvm.add"(%144, %140) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %146 = "llvm.call"(%94, %15) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %147 = "llvm.call"(%94, %16) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %148 = "llvm.xor"(%147, %146) : (i64, i64) -> i64
    %149 = "llvm.call"(%94, %17) <{CConv = #llvm.cconv<fastcc>, callee = @fd_ulong_rotate_right, fastmathFlags = #llvm.fastmath<none>}> : (i64, i32) -> i64
    %150 = "llvm.xor"(%148, %149) : (i64, i64) -> i64
    %151 = "llvm.xor"(%95, %96) : (i64, i64) -> i64
    %152 = "llvm.and"(%94, %151) : (i64, i64) -> i64
    %153 = "llvm.and"(%95, %96) : (i64, i64) -> i64
    %154 = "llvm.xor"(%152, %153) : (i64, i64) -> i64
    %155 = "llvm.add"(%145, %97) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %156 = "llvm.add"(%145, %154) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %157 = "llvm.add"(%156, %150) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %158 = "llvm.icmp"(%103, %25) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%158, %157, %94, %95, %96, %103, %100, %101, %102, %155)[^bb4, ^bb3] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 0, 9>}> : (i1, i64, i64, i64, i64, i64, i64, i64, i64, i64) -> ()
  ^bb4:  // pred: ^bb3
    %159 = "llvm.add"(%157, %49) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.store"(%159, %arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %160 = "llvm.add"(%94, %48) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.store"(%160, %27) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %161 = "llvm.add"(%95, %47) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.store"(%161, %28) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %162 = "llvm.add"(%96, %46) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.store"(%162, %29) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %163 = "llvm.add"(%155, %45) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.store"(%163, %30) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %164 = "llvm.add"(%102, %44) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.store"(%164, %31) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %165 = "llvm.add"(%101, %43) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.store"(%165, %32) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %166 = "llvm.add"(%100, %42) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.store"(%166, %33) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %167 = "llvm.getelementptr"(%50, %18) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.lifetime.end"(%26) <{size = 128 : i64}> : (!llvm.ptr) -> ()
    %168 = "llvm.add"(%51, %12) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %169 = "llvm.icmp"(%168, %8) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%169, %166, %165, %164, %163, %162, %161, %160, %159, %167, %168)[^bb5, ^bb1] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 0, 10>}> : (i1, i64, i64, i64, i64, i64, i64, i64, i64, !llvm.ptr, i64) -> ()
  ^bb5:  // pred: ^bb4
    "llvm.return"() : () -> ()
}
]

set_option maxRecDepth 100000 in
def fd_sha512_core_ref : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [] :=
  [sllvm_cfg_of| fd_sha512_core_ref_region with
    @fd_ulong_bswap := fd_ulong_bswap,
    @fd_ulong_rotate_right := fd_ulong_rotate_right]

/-! ## Evaluation

The lift -- three loops, cross-block values threaded into block arguments,
`fshr` and `bswap` -- checked end to end against FIPS 180-4: one compression of
the padded `"abc"` block, and two of the 896-bit two-block example, starting
from the SHA-512 initial hash value. The round constants are installed as the
global `@fd_sha512_core_ref.K`, the state and message as plain blocks.
-/

/-- `ws` packed little-endian, `wbytes` bytes per word. -/
private def packLE (ws : List Nat) (wbytes : Nat) : Nat :=
  (ws.zipIdx).foldl (fun acc (w, i) => acc + w * 2 ^ (8 * wbytes * i)) 0

private def kWords : List Nat := [0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
  0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
  0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
  0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
  0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
  0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
  0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
  0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
  0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
  0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
  0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

private def ivWords : List Nat := [0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b,
  0xa54ff53a5f1d36f1, 0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

/-- `"abc"` padded to one SHA-512 block: the message, `0x80`, zeroes, and the
128-bit big-endian bit length `24` in the last bytes. -/
private def abcBlock : List Nat := [0x61, 0x62, 0x63, 0x80] ++ List.replicate 123 0 ++ [0x18]

/-- A block of `n` bytes holding `v`, installed at the next free id. -/
private def install (s : GlobalState) (n : Nat) (v : Nat) : GlobalState × Pointer :=
  let p : Pointer := ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩
  let s := s.afterAlloca (8 * n)
  ({ s with mem := s.mem.splice p (BitVec.ofNat (8 * n) v) }, p)

private def runOn (msg : List Nat) (cnt : Nat) : Option (List Nat) := Id.run do
  let s₀ : GlobalState := ⟨⟨0⟩, ⟨∅⟩, ∅⟩
  let (s₁, kp) := install s₀ 640 (packLE kWords 8)
  let s₁ := { s₁ with globals := s₁.globals.insert "fd_sha512_core_ref.K" kp }
  let (s₂, stp) := install s₁ 64 (packLE ivWords 8)
  let (s₃, bp) := install s₂ (128 * cnt) (packLE msg 1)
  let V := Ctxt.Valuation.ofHVector
    [(PoisonOr.value (BitVec.ofNat 64 cnt) : LLVM.IntW 64), PoisonOr.value bp, PoisonOr.value stp]ₕ
  match Cfg.eval 2000 fd_sha512_core_ref V s₃ with
  | some (.value (_, s')) =>
      match s'.mem.live? stp.id with
      | some blk => some ((List.range 8).map fun i => (blk.bytes.extractLsb' (64 * i) 64).toNat)
      | none => none
  | _ => none

/-- SHA-512("abc"), FIPS 180-4 example. -/
private def abcDigest : List Nat := [0xddaf35a193617aba, 0xcc417349ae204131, 0x12e6fa4e89a97ea2,
  0x0a9eeee64b55d39a, 0x2192992a274fc1a8, 0x36ba3c23a3feebbd, 0x454d4423643ce80e, 0x2a9ac94fa54ca49f]


/-- The FIPS 180-4 two-block example, padded to 256 bytes. -/
private def twoBlock : List Nat :=
  ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno" ++
    "ijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu").toList.map Char.toNat
    ++ [0x80] ++ List.replicate 141 0 ++ [0x03, 0x80]

private def twoBlockDigest : List Nat := [0x8e959b75dae313da, 0x8cf4f72814fc143f, 0x8f7779c6eb9f7fa1,
  0x7299aeadb6889018, 0x501d289e4900f7e4, 0x331b99dec4b5433a, 0xc7d329eeb6dd2654, 0x5e96e55b874be909]

#guard runOn abcBlock 1 == some abcDigest
#guard runOn twoBlock 2 == some twoBlockDigest

end Firedancer.Common

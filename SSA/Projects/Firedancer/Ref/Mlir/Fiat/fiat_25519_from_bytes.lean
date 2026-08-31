/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fiat_25519_from_bytes_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 31 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 127 : i8}> : () -> i8
    %2 = "llvm.mlir.constant"() <{value = 44 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 30 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 36 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 29 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 28 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 20 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 27 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 12 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 25 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 47 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> i64
    %15 = "llvm.mlir.constant"() <{value = 39 : i64}> : () -> i64
    %16 = "llvm.mlir.constant"() <{value = 23 : i64}> : () -> i64
    %17 = "llvm.mlir.constant"() <{value = 22 : i64}> : () -> i64
    %18 = "llvm.mlir.constant"() <{value = 21 : i64}> : () -> i64
    %19 = "llvm.mlir.constant"() <{value = 15 : i64}> : () -> i64
    %20 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %21 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %22 = "llvm.mlir.constant"() <{value = 50 : i64}> : () -> i64
    %23 = "llvm.mlir.constant"() <{value = 18 : i64}> : () -> i64
    %24 = "llvm.mlir.constant"() <{value = 42 : i64}> : () -> i64
    %25 = "llvm.mlir.constant"() <{value = 17 : i64}> : () -> i64
    %26 = "llvm.mlir.constant"() <{value = 34 : i64}> : () -> i64
    %27 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %28 = "llvm.mlir.constant"() <{value = 14 : i64}> : () -> i64
    %29 = "llvm.mlir.constant"() <{value = 10 : i64}> : () -> i64
    %30 = "llvm.mlir.constant"() <{value = 13 : i64}> : () -> i64
    %31 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %32 = "llvm.mlir.constant"() <{value = 45 : i64}> : () -> i64
    %33 = "llvm.mlir.constant"() <{value = 11 : i64}> : () -> i64
    %34 = "llvm.mlir.constant"() <{value = 37 : i64}> : () -> i64
    %35 = "llvm.mlir.constant"() <{value = 9 : i64}> : () -> i64
    %36 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %37 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %38 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %39 = "llvm.mlir.constant"() <{value = 48 : i64}> : () -> i64
    %40 = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
    %41 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %42 = "llvm.mlir.constant"() <{value = 1970324836974592 : i64}> : () -> i64
    %43 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %44 = "llvm.mlir.constant"() <{value = 2216615441596416 : i64}> : () -> i64
    %45 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %46 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %47 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %48 = "llvm.getelementptr"(%arg1, %0) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %49 = "llvm.load"(%48) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %50 = "llvm.and"(%49, %1) : (i8, i8) -> i8
    %51 = "llvm.zext"(%50) : (i8) -> i64
    %52 = "llvm.shl"(%51, %2) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %53 = "llvm.getelementptr"(%arg1, %3) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %54 = "llvm.load"(%53) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %55 = "llvm.zext"(%54) : (i8) -> i64
    %56 = "llvm.shl"(%55, %4) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %57 = "llvm.getelementptr"(%arg1, %5) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %58 = "llvm.load"(%57) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %59 = "llvm.zext"(%58) : (i8) -> i64
    %60 = "llvm.shl"(%59, %6) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %61 = "llvm.getelementptr"(%arg1, %6) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %62 = "llvm.load"(%61) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %63 = "llvm.zext"(%62) : (i8) -> i64
    %64 = "llvm.shl"(%63, %7) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %65 = "llvm.getelementptr"(%arg1, %8) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %66 = "llvm.load"(%65) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %67 = "llvm.zext"(%66) : (i8) -> i64
    %68 = "llvm.shl"(%67, %9) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %69 = "llvm.getelementptr"(%arg1, %10) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %70 = "llvm.load"(%69) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %71 = "llvm.zext"(%70) : (i8) -> i64
    %72 = "llvm.shl"(%71, %11) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %73 = "llvm.getelementptr"(%arg1, %12) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %74 = "llvm.load"(%73) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %75 = "llvm.zext"(%74) : (i8) -> i64
    %76 = "llvm.shl"(%75, %13) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %77 = "llvm.getelementptr"(%arg1, %14) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %78 = "llvm.load"(%77) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %79 = "llvm.zext"(%78) : (i8) -> i64
    %80 = "llvm.shl"(%79, %15) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %81 = "llvm.getelementptr"(%arg1, %16) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %82 = "llvm.load"(%81) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %83 = "llvm.zext"(%82) : (i8) -> i64
    %84 = "llvm.shl"(%83, %0) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %85 = "llvm.getelementptr"(%arg1, %17) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %86 = "llvm.load"(%85) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %87 = "llvm.zext"(%86) : (i8) -> i64
    %88 = "llvm.shl"(%87, %16) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %89 = "llvm.getelementptr"(%arg1, %18) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %90 = "llvm.load"(%89) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %91 = "llvm.zext"(%90) : (i8) -> i64
    %92 = "llvm.shl"(%91, %19) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %93 = "llvm.getelementptr"(%arg1, %7) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %94 = "llvm.load"(%93) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %95 = "llvm.zext"(%94) : (i8) -> i64
    %96 = "llvm.shl"(%95, %20) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %97 = "llvm.getelementptr"(%arg1, %21) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %98 = "llvm.load"(%97) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %99 = "llvm.zext"(%98) : (i8) -> i64
    %100 = "llvm.shl"(%99, %22) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %101 = "llvm.getelementptr"(%arg1, %23) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %102 = "llvm.load"(%101) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %103 = "llvm.zext"(%102) : (i8) -> i64
    %104 = "llvm.shl"(%103, %24) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %105 = "llvm.getelementptr"(%arg1, %25) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %106 = "llvm.load"(%105) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %107 = "llvm.zext"(%106) : (i8) -> i64
    %108 = "llvm.shl"(%107, %26) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %109 = "llvm.getelementptr"(%arg1, %27) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %110 = "llvm.load"(%109) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %111 = "llvm.zext"(%110) : (i8) -> i64
    %112 = "llvm.shl"(%111, %10) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %113 = "llvm.getelementptr"(%arg1, %19) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %114 = "llvm.load"(%113) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %115 = "llvm.zext"(%114) : (i8) -> i64
    %116 = "llvm.shl"(%115, %23) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %117 = "llvm.getelementptr"(%arg1, %28) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %118 = "llvm.load"(%117) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %119 = "llvm.zext"(%118) : (i8) -> i64
    %120 = "llvm.shl"(%119, %29) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %121 = "llvm.getelementptr"(%arg1, %30) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %122 = "llvm.load"(%121) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %123 = "llvm.zext"(%122) : (i8) -> i64
    %124 = "llvm.shl"(%123, %31) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %125 = "llvm.getelementptr"(%arg1, %9) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %126 = "llvm.load"(%125) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %127 = "llvm.zext"(%126) : (i8) -> i64
    %128 = "llvm.shl"(%127, %32) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %129 = "llvm.getelementptr"(%arg1, %33) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %130 = "llvm.load"(%129) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %131 = "llvm.zext"(%130) : (i8) -> i64
    %132 = "llvm.shl"(%131, %34) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %133 = "llvm.getelementptr"(%arg1, %29) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %134 = "llvm.load"(%133) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %135 = "llvm.zext"(%134) : (i8) -> i64
    %136 = "llvm.shl"(%135, %5) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %137 = "llvm.getelementptr"(%arg1, %35) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %138 = "llvm.load"(%137) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %139 = "llvm.zext"(%138) : (i8) -> i64
    %140 = "llvm.shl"(%139, %18) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %141 = "llvm.getelementptr"(%arg1, %36) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %142 = "llvm.load"(%141) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %143 = "llvm.zext"(%142) : (i8) -> i64
    %144 = "llvm.shl"(%143, %30) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %145 = "llvm.getelementptr"(%arg1, %20) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %146 = "llvm.load"(%145) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %147 = "llvm.zext"(%146) : (i8) -> i64
    %148 = "llvm.shl"(%147, %37) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %149 = "llvm.getelementptr"(%arg1, %38) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %150 = "llvm.load"(%149) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %151 = "llvm.zext"(%150) : (i8) -> i64
    %152 = "llvm.shl"(%151, %39) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %153 = "llvm.getelementptr"(%arg1, %37) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %154 = "llvm.load"(%153) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %155 = "llvm.zext"(%154) : (i8) -> i64
    %156 = "llvm.shl"(%155, %40) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %157 = "llvm.getelementptr"(%arg1, %11) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %158 = "llvm.load"(%157) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %159 = "llvm.zext"(%158) : (i8) -> i64
    %160 = "llvm.shl"(%159, %41) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %161 = "llvm.load"(%arg1) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %162 = "llvm.zext"(%161) : (i32) -> i64
    %163 = "llvm.or"(%156, %162) : (i64, i64) -> i64
    %164 = "llvm.or"(%163, %160) : (i64, i64) -> i64
    %165 = "llvm.and"(%152, %42) : (i64, i64) -> i64
    %166 = "llvm.or"(%164, %165) : (i64, i64) -> i64
    %167 = "llvm.lshr"(%151, %43) : (i64, i64) -> i64
    %168 = "llvm.and"(%128, %44) : (i64, i64) -> i64
    %169 = "llvm.or"(%132, %168) : (i64, i64) -> i64
    %170 = "llvm.or"(%169, %136) : (i64, i64) -> i64
    %171 = "llvm.or"(%170, %140) : (i64, i64) -> i64
    %172 = "llvm.or"(%171, %144) : (i64, i64) -> i64
    %173 = "llvm.or"(%172, %148) : (i64, i64) -> i64
    %174 = "llvm.or"(%173, %167) : (i64, i64) -> i64
    %175 = "llvm.lshr"(%127, %38) : (i64, i64) -> i64
    %176 = "llvm.or"(%104, %100) : (i64, i64) -> i64
    %177 = "llvm.or"(%176, %108) : (i64, i64) -> i64
    %178 = "llvm.or"(%177, %112) : (i64, i64) -> i64
    %179 = "llvm.or"(%178, %116) : (i64, i64) -> i64
    %180 = "llvm.or"(%179, %120) : (i64, i64) -> i64
    %181 = "llvm.or"(%180, %124) : (i64, i64) -> i64
    %182 = "llvm.add"(%181, %175) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %183 = "llvm.and"(%182, %45) : (i64, i64) -> i64
    %184 = "llvm.lshr"(%182, %46) : (i64, i64) -> i64
    %185 = "llvm.or"(%80, %76) : (i64, i64) -> i64
    %186 = "llvm.or"(%185, %84) : (i64, i64) -> i64
    %187 = "llvm.or"(%186, %88) : (i64, i64) -> i64
    %188 = "llvm.or"(%187, %92) : (i64, i64) -> i64
    %189 = "llvm.or"(%188, %96) : (i64, i64) -> i64
    %190 = "llvm.add"(%189, %184) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %191 = "llvm.and"(%190, %45) : (i64, i64) -> i64
    %192 = "llvm.lshr"(%190, %46) : (i64, i64) -> i64
    %193 = "llvm.or"(%52, %56) : (i64, i64) -> i64
    %194 = "llvm.or"(%193, %60) : (i64, i64) -> i64
    %195 = "llvm.or"(%194, %64) : (i64, i64) -> i64
    %196 = "llvm.or"(%195, %68) : (i64, i64) -> i64
    %197 = "llvm.or"(%196, %72) : (i64, i64) -> i64
    %198 = "llvm.add"(%197, %192) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    "llvm.store"(%166, %arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %199 = "llvm.getelementptr"(%arg0, %47) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%174, %199) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %200 = "llvm.getelementptr"(%arg0, %31) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%183, %200) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %201 = "llvm.getelementptr"(%arg0, %43) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%191, %201) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %202 = "llvm.getelementptr"(%arg0, %11) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%198, %202) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

def fiat_25519_from_bytes : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [] :=
  [sllvm_cfg_of| fiat_25519_from_bytes_region]

end Firedancer.Ref

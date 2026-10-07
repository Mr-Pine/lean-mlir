/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/ref/region/fiat_25519_from_bytes.mlir
module

public import SSA.Projects.SLLVM.Cfg

@[expose] public section

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fiat_25519_from_bytes_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 31 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 127 : i8}> : () -> i8
    %2 = "llvm.mlir.constant"() <{value = 44 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 36 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 29 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 28 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 20 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 12 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 47 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 39 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 23 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 21 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = 15 : i64}> : () -> i64
    %15 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %16 = "llvm.mlir.constant"() <{value = 50 : i64}> : () -> i64
    %17 = "llvm.mlir.constant"() <{value = 18 : i64}> : () -> i64
    %18 = "llvm.mlir.constant"() <{value = 42 : i64}> : () -> i64
    %19 = "llvm.mlir.constant"() <{value = 34 : i64}> : () -> i64
    %20 = "llvm.mlir.constant"() <{value = 10 : i64}> : () -> i64
    %21 = "llvm.mlir.constant"() <{value = 13 : i64}> : () -> i64
    %22 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %23 = "llvm.mlir.constant"() <{value = 45 : i64}> : () -> i64
    %24 = "llvm.mlir.constant"() <{value = 37 : i64}> : () -> i64
    %25 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %26 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %27 = "llvm.mlir.constant"() <{value = 48 : i64}> : () -> i64
    %28 = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
    %29 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %30 = "llvm.mlir.constant"() <{value = 1970324836974592 : i64}> : () -> i64
    %31 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %32 = "llvm.mlir.constant"() <{value = 2216615441596416 : i64}> : () -> i64
    %33 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %34 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %35 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 31>}> : (!llvm.ptr) -> !llvm.ptr
    %36 = "llvm.load"(%35) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %37 = "llvm.and"(%36, %1) : (i8, i8) -> i8
    %38 = "llvm.zext"(%37) : (i8) -> i64
    %39 = "llvm.shl"(%38, %2) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %40 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 30>}> : (!llvm.ptr) -> !llvm.ptr
    %41 = "llvm.load"(%40) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %42 = "llvm.zext"(%41) : (i8) -> i64
    %43 = "llvm.shl"(%42, %3) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %44 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 29>}> : (!llvm.ptr) -> !llvm.ptr
    %45 = "llvm.load"(%44) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %46 = "llvm.zext"(%45) : (i8) -> i64
    %47 = "llvm.shl"(%46, %5) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %48 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 28>}> : (!llvm.ptr) -> !llvm.ptr
    %49 = "llvm.load"(%48) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %50 = "llvm.zext"(%49) : (i8) -> i64
    %51 = "llvm.shl"(%50, %6) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %52 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 27>}> : (!llvm.ptr) -> !llvm.ptr
    %53 = "llvm.load"(%52) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %54 = "llvm.zext"(%53) : (i8) -> i64
    %55 = "llvm.shl"(%54, %7) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %56 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 26>}> : (!llvm.ptr) -> !llvm.ptr
    %57 = "llvm.load"(%56) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %58 = "llvm.zext"(%57) : (i8) -> i64
    %59 = "llvm.shl"(%58, %9) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %60 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 25>}> : (!llvm.ptr) -> !llvm.ptr
    %61 = "llvm.load"(%60) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %62 = "llvm.zext"(%61) : (i8) -> i64
    %63 = "llvm.shl"(%62, %10) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %64 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 24>}> : (!llvm.ptr) -> !llvm.ptr
    %65 = "llvm.load"(%64) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %66 = "llvm.zext"(%65) : (i8) -> i64
    %67 = "llvm.shl"(%66, %11) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %68 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 23>}> : (!llvm.ptr) -> !llvm.ptr
    %69 = "llvm.load"(%68) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %70 = "llvm.zext"(%69) : (i8) -> i64
    %71 = "llvm.shl"(%70, %0) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %72 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 22>}> : (!llvm.ptr) -> !llvm.ptr
    %73 = "llvm.load"(%72) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %74 = "llvm.zext"(%73) : (i8) -> i64
    %75 = "llvm.shl"(%74, %12) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %76 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 21>}> : (!llvm.ptr) -> !llvm.ptr
    %77 = "llvm.load"(%76) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %78 = "llvm.zext"(%77) : (i8) -> i64
    %79 = "llvm.shl"(%78, %14) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %80 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 20>}> : (!llvm.ptr) -> !llvm.ptr
    %81 = "llvm.load"(%80) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %82 = "llvm.zext"(%81) : (i8) -> i64
    %83 = "llvm.shl"(%82, %15) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %84 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 19>}> : (!llvm.ptr) -> !llvm.ptr
    %85 = "llvm.load"(%84) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %86 = "llvm.zext"(%85) : (i8) -> i64
    %87 = "llvm.shl"(%86, %16) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %88 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 18>}> : (!llvm.ptr) -> !llvm.ptr
    %89 = "llvm.load"(%88) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %90 = "llvm.zext"(%89) : (i8) -> i64
    %91 = "llvm.shl"(%90, %18) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %92 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 17>}> : (!llvm.ptr) -> !llvm.ptr
    %93 = "llvm.load"(%92) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %94 = "llvm.zext"(%93) : (i8) -> i64
    %95 = "llvm.shl"(%94, %19) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %96 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
    %97 = "llvm.load"(%96) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %98 = "llvm.zext"(%97) : (i8) -> i64
    %99 = "llvm.shl"(%98, %8) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %100 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 15>}> : (!llvm.ptr) -> !llvm.ptr
    %101 = "llvm.load"(%100) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %102 = "llvm.zext"(%101) : (i8) -> i64
    %103 = "llvm.shl"(%102, %17) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %104 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 14>}> : (!llvm.ptr) -> !llvm.ptr
    %105 = "llvm.load"(%104) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %106 = "llvm.zext"(%105) : (i8) -> i64
    %107 = "llvm.shl"(%106, %20) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %108 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 13>}> : (!llvm.ptr) -> !llvm.ptr
    %109 = "llvm.load"(%108) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %110 = "llvm.zext"(%109) : (i8) -> i64
    %111 = "llvm.shl"(%110, %22) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %112 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 12>}> : (!llvm.ptr) -> !llvm.ptr
    %113 = "llvm.load"(%112) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %114 = "llvm.zext"(%113) : (i8) -> i64
    %115 = "llvm.shl"(%114, %23) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %116 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 11>}> : (!llvm.ptr) -> !llvm.ptr
    %117 = "llvm.load"(%116) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %118 = "llvm.zext"(%117) : (i8) -> i64
    %119 = "llvm.shl"(%118, %24) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %120 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 10>}> : (!llvm.ptr) -> !llvm.ptr
    %121 = "llvm.load"(%120) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %122 = "llvm.zext"(%121) : (i8) -> i64
    %123 = "llvm.shl"(%122, %4) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %124 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 9>}> : (!llvm.ptr) -> !llvm.ptr
    %125 = "llvm.load"(%124) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %126 = "llvm.zext"(%125) : (i8) -> i64
    %127 = "llvm.shl"(%126, %13) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %128 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 8>}> : (!llvm.ptr) -> !llvm.ptr
    %129 = "llvm.load"(%128) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %130 = "llvm.zext"(%129) : (i8) -> i64
    %131 = "llvm.shl"(%130, %21) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %132 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 7>}> : (!llvm.ptr) -> !llvm.ptr
    %133 = "llvm.load"(%132) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %134 = "llvm.zext"(%133) : (i8) -> i64
    %135 = "llvm.shl"(%134, %25) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %136 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 6>}> : (!llvm.ptr) -> !llvm.ptr
    %137 = "llvm.load"(%136) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %138 = "llvm.zext"(%137) : (i8) -> i64
    %139 = "llvm.shl"(%138, %27) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %140 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 5>}> : (!llvm.ptr) -> !llvm.ptr
    %141 = "llvm.load"(%140) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %142 = "llvm.zext"(%141) : (i8) -> i64
    %143 = "llvm.shl"(%142, %28) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %144 = "llvm.getelementptr"(%arg1) <{elem_type = i8, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    %145 = "llvm.load"(%144) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i8
    %146 = "llvm.zext"(%145) : (i8) -> i64
    %147 = "llvm.shl"(%146, %29) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %148 = "llvm.load"(%arg1) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %149 = "llvm.zext"(%148) : (i32) -> i64
    %150 = "llvm.or"(%143, %149) : (i64, i64) -> i64
    %151 = "llvm.or"(%150, %147) : (i64, i64) -> i64
    %152 = "llvm.and"(%139, %30) : (i64, i64) -> i64
    %153 = "llvm.or"(%151, %152) : (i64, i64) -> i64
    %154 = "llvm.lshr"(%138, %31) : (i64, i64) -> i64
    %155 = "llvm.and"(%115, %32) : (i64, i64) -> i64
    %156 = "llvm.or"(%119, %155) : (i64, i64) -> i64
    %157 = "llvm.or"(%156, %123) : (i64, i64) -> i64
    %158 = "llvm.or"(%157, %127) : (i64, i64) -> i64
    %159 = "llvm.or"(%158, %131) : (i64, i64) -> i64
    %160 = "llvm.or"(%159, %135) : (i64, i64) -> i64
    %161 = "llvm.or"(%160, %154) : (i64, i64) -> i64
    %162 = "llvm.lshr"(%114, %26) : (i64, i64) -> i64
    %163 = "llvm.or"(%91, %87) : (i64, i64) -> i64
    %164 = "llvm.or"(%163, %95) : (i64, i64) -> i64
    %165 = "llvm.or"(%164, %99) : (i64, i64) -> i64
    %166 = "llvm.or"(%165, %103) : (i64, i64) -> i64
    %167 = "llvm.or"(%166, %107) : (i64, i64) -> i64
    %168 = "llvm.or"(%167, %111) : (i64, i64) -> i64
    %169 = "llvm.add"(%168, %162) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %170 = "llvm.and"(%169, %33) : (i64, i64) -> i64
    %171 = "llvm.lshr"(%169, %34) : (i64, i64) -> i64
    %172 = "llvm.or"(%67, %63) : (i64, i64) -> i64
    %173 = "llvm.or"(%172, %71) : (i64, i64) -> i64
    %174 = "llvm.or"(%173, %75) : (i64, i64) -> i64
    %175 = "llvm.or"(%174, %79) : (i64, i64) -> i64
    %176 = "llvm.or"(%175, %83) : (i64, i64) -> i64
    %177 = "llvm.add"(%176, %171) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %178 = "llvm.and"(%177, %33) : (i64, i64) -> i64
    %179 = "llvm.lshr"(%177, %34) : (i64, i64) -> i64
    %180 = "llvm.or"(%39, %43) : (i64, i64) -> i64
    %181 = "llvm.or"(%180, %47) : (i64, i64) -> i64
    %182 = "llvm.or"(%181, %51) : (i64, i64) -> i64
    %183 = "llvm.or"(%182, %55) : (i64, i64) -> i64
    %184 = "llvm.or"(%183, %59) : (i64, i64) -> i64
    %185 = "llvm.add"(%184, %179) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    "llvm.store"(%153, %arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %186 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%161, %186) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %187 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%170, %187) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %188 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%178, %188) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %189 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%185, %189) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

sllvm_cfg_def fiat_25519_from_bytes : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [] :=
  [sllvm_cfg_of| fiat_25519_from_bytes_region]

end Firedancer.Ref

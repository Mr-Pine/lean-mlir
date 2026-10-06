module
public import SSA.Projects.RIR.Syntax.Elab
/-! Verbatim function region from the pinned compiler-generated reduce64 MLIR.
See MLIR/generated/agave_avx2_field_reduce64.mlir and source-manifest.json. -/
namespace Agave.Ed25519.Reduce64
@[expose] public section
mlir_def program :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = dense<26> : vector<4xi64>}> : () -> vector<4xi64>
    %2 = "llvm.mlir.constant"() <{value = dense<67108863> : vector<4xi64>}> : () -> vector<4xi64>
    %3 = "llvm.mlir.constant"() <{value = 128 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 160 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 64 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = dense<25> : vector<4xi64>}> : () -> vector<4xi64>
    %7 = "llvm.mlir.constant"() <{value = dense<33554431> : vector<4xi64>}> : () -> vector<4xi64>
    %8 = "llvm.mlir.constant"() <{value = 192 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 96 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 224 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 256 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 288 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = dense<51> : vector<4xi64>}> : () -> vector<4xi64>
    %14 = "llvm.mlir.constant"() <{value = dense<19> : vector<4xi64>}> : () -> vector<4xi64>
    %15 = "llvm.mlir.poison"() : () -> i32
    %16 = "llvm.mlir.constant"() <{value = 67108863 : i32}> : () -> i32
    %17 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %18 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %19 = "llvm.insertelement"(%17, %16, %18) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %20 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %21 = "llvm.insertelement"(%19, %15, %20) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %22 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %23 = "llvm.insertelement"(%21, %16, %22) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %24 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %25 = "llvm.insertelement"(%23, %15, %24) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %26 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %27 = "llvm.insertelement"(%25, %16, %26) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %28 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %29 = "llvm.insertelement"(%27, %15, %28) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %30 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %31 = "llvm.insertelement"(%29, %16, %30) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %32 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %33 = "llvm.insertelement"(%31, %15, %32) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %34 = "llvm.mlir.constant"() <{value = 33554431 : i32}> : () -> i32
    %35 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %36 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %37 = "llvm.insertelement"(%35, %34, %36) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %38 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %39 = "llvm.insertelement"(%37, %15, %38) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %40 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %41 = "llvm.insertelement"(%39, %34, %40) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %42 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %43 = "llvm.insertelement"(%41, %15, %42) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %44 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %45 = "llvm.insertelement"(%43, %34, %44) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %46 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %47 = "llvm.insertelement"(%45, %15, %46) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %48 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %49 = "llvm.insertelement"(%47, %34, %48) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %50 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %51 = "llvm.insertelement"(%49, %15, %50) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope1}> : () -> ()
    %52 = "llvm.getelementptr"(%arg1, %0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %53 = "llvm.load"(%arg1) <{alias_scopes = [#alias_scope2, #alias_scope1], alignment = 32 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> vector<4xi64>
    %54 = "llvm.load"(%52) <{alias_scopes = [#alias_scope2, #alias_scope1], alignment = 32 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> vector<4xi64>
    %55 = "llvm.lshr"(%53, %1) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %56 = "llvm.add"(%54, %55) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %57 = "llvm.and"(%53, %2) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %58 = "llvm.getelementptr"(%arg1, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %59 = "llvm.getelementptr"(%arg1, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %60 = "llvm.load"(%58) <{alias_scopes = [#alias_scope3, #alias_scope1], alignment = 32 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> vector<4xi64>
    %61 = "llvm.load"(%59) <{alias_scopes = [#alias_scope3, #alias_scope1], alignment = 32 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> vector<4xi64>
    %62 = "llvm.lshr"(%60, %1) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %63 = "llvm.add"(%61, %62) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %64 = "llvm.and"(%60, %2) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %65 = "llvm.getelementptr"(%arg1, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %66 = "llvm.load"(%65) <{alias_scopes = [#alias_scope4, #alias_scope1], alignment = 32 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> vector<4xi64>
    %67 = "llvm.lshr"(%56, %6) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %68 = "llvm.add"(%66, %67) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %69 = "llvm.and"(%56, %7) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %70 = "llvm.getelementptr"(%arg1, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %71 = "llvm.load"(%70) <{alias_scopes = [#alias_scope5, #alias_scope1], alignment = 32 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> vector<4xi64>
    %72 = "llvm.lshr"(%63, %6) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %73 = "llvm.add"(%71, %72) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %74 = "llvm.and"(%63, %7) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %75 = "llvm.getelementptr"(%arg1, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %76 = "llvm.load"(%75) <{alias_scopes = [#alias_scope6, #alias_scope1], alignment = 32 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> vector<4xi64>
    %77 = "llvm.lshr"(%68, %1) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %78 = "llvm.add"(%76, %77) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %79 = "llvm.getelementptr"(%arg1, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %80 = "llvm.load"(%79) <{alias_scopes = [#alias_scope7, #alias_scope1], alignment = 32 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> vector<4xi64>
    %81 = "llvm.lshr"(%73, %1) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %82 = "llvm.add"(%80, %81) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %83 = "llvm.lshr"(%78, %6) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %84 = "llvm.add"(%83, %64) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %85 = "llvm.getelementptr"(%arg1, %11) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %86 = "llvm.load"(%85) <{alias_scopes = [#alias_scope8, #alias_scope1], alignment = 32 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> vector<4xi64>
    %87 = "llvm.lshr"(%82, %6) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %88 = "llvm.add"(%87, %86) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %89 = "llvm.lshr"(%84, %1) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %90 = "llvm.add"(%89, %74) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %91 = "llvm.getelementptr"(%arg1, %12) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %92 = "llvm.load"(%91) <{alias_scopes = [#alias_scope9, #alias_scope1], alignment = 32 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> vector<4xi64>
    %93 = "llvm.lshr"(%88, %1) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %94 = "llvm.add"(%93, %92) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %95 = "llvm.lshr"(%94, %6) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %96 = "llvm.and"(%95, %2) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %97 = "llvm.lshr"(%94, %13) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %98 = "llvm.mul"(%96, %14) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %99 = "llvm.mul"(%97, %14) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %100 = "llvm.add"(%98, %57) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %101 = "llvm.add"(%99, %69) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %102 = "llvm.lshr"(%100, %1) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %103 = "llvm.add"(%101, %102) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %104 = "llvm.bitcast"(%100) : (vector<4xi64>) -> vector<8xi32>
    %105 = "llvm.and"(%104, %33) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %106 = "llvm.bitcast"(%103) : (vector<4xi64>) -> vector<8xi32>
    %107 = "llvm.shufflevector"(%105, %106) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %108 = "llvm.bitcast"(%68) : (vector<4xi64>) -> vector<8xi32>
    %109 = "llvm.and"(%108, %33) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %110 = "llvm.bitcast"(%78) : (vector<4xi64>) -> vector<8xi32>
    %111 = "llvm.and"(%110, %51) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %112 = "llvm.shufflevector"(%109, %111) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %113 = "llvm.bitcast"(%90) : (vector<4xi64>) -> vector<8xi32>
    %114 = "llvm.bitcast"(%84) : (vector<4xi64>) -> vector<8xi32>
    %115 = "llvm.and"(%114, %33) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %116 = "llvm.shufflevector"(%115, %113) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %117 = "llvm.bitcast"(%73) : (vector<4xi64>) -> vector<8xi32>
    %118 = "llvm.and"(%117, %33) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %119 = "llvm.bitcast"(%82) : (vector<4xi64>) -> vector<8xi32>
    %120 = "llvm.and"(%119, %51) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %121 = "llvm.shufflevector"(%118, %120) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %122 = "llvm.bitcast"(%88) : (vector<4xi64>) -> vector<8xi32>
    %123 = "llvm.and"(%122, %33) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %124 = "llvm.bitcast"(%94) : (vector<4xi64>) -> vector<8xi32>
    %125 = "llvm.and"(%124, %51) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %126 = "llvm.shufflevector"(%123, %125) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%107, %arg0) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %127 = "llvm.getelementptr"(%arg0, %0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%112, %127) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %128 = "llvm.getelementptr"(%arg0, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%116, %128) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %129 = "llvm.getelementptr"(%arg0, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%121, %129) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %130 = "llvm.getelementptr"(%arg0, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%126, %130) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
end
end Agave.Ed25519.Reduce64

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_quad_mul_fast

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_curve25519_into_precomputed_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %2 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %4 = "llvm.mlir.poison"() : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 8796093022207 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 8796093022189 : i64}> : () -> i64
    %7 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %8 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %9 = "llvm.insertelement"(%7, %6, %8) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %10 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %11 = "llvm.insertelement"(%9, %4, %10) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %12 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %13 = "llvm.insertelement"(%11, %4, %12) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %14 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %15 = "llvm.insertelement"(%13, %4, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %16 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %17 = "llvm.insertelement"(%15, %5, %16) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %18 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %19 = "llvm.insertelement"(%17, %4, %18) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %20 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %21 = "llvm.insertelement"(%19, %4, %20) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %22 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %23 = "llvm.insertelement"(%21, %4, %22) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %24 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %25 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %26 = "llvm.insertelement"(%24, %5, %25) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %27 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %28 = "llvm.insertelement"(%26, %4, %27) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %29 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %30 = "llvm.insertelement"(%28, %4, %29) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %31 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %32 = "llvm.insertelement"(%30, %4, %31) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %33 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %34 = "llvm.insertelement"(%32, %5, %33) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %35 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %36 = "llvm.insertelement"(%34, %4, %35) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %37 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %38 = "llvm.insertelement"(%36, %4, %37) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %39 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %40 = "llvm.insertelement"(%38, %4, %39) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %41 = "llvm.mlir.constant"() <{value = 1099511627775 : i64}> : () -> i64
    %42 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %43 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %44 = "llvm.insertelement"(%42, %5, %43) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %45 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %46 = "llvm.insertelement"(%44, %4, %45) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %47 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %48 = "llvm.insertelement"(%46, %4, %47) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %49 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %50 = "llvm.insertelement"(%48, %4, %49) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %51 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %52 = "llvm.insertelement"(%50, %41, %51) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %53 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %54 = "llvm.insertelement"(%52, %4, %53) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %55 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %56 = "llvm.insertelement"(%54, %4, %55) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %57 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %58 = "llvm.insertelement"(%56, %4, %57) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %59 = "llvm.mlir.constant"() <{value = dense<[-159383552, -159383552, -159383552, -159383552, -1048576, -1048576, -1048576, -1048576]> : vector<8xi64>}> : () -> vector<8xi64>
    %60 = "llvm.mlir.constant"() <{value = dense<-1048576> : vector<8xi64>}> : () -> vector<8xi64>
    %61 = "llvm.mlir.constant"() <{value = dense<43> : vector<8xi64>}> : () -> vector<8xi64>
    %62 = "llvm.mlir.constant"() <{value = dense<[43, 43, 43, 43, 40, 40, 40, 40]> : vector<8xi64>}> : () -> vector<8xi64>
    %63 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %64 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %65 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %66 = "llvm.insertelement"(%64, %4, %65) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %67 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %68 = "llvm.insertelement"(%66, %4, %67) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %69 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %70 = "llvm.insertelement"(%68, %4, %69) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %71 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %72 = "llvm.insertelement"(%70, %4, %71) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %73 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %74 = "llvm.insertelement"(%72, %63, %73) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %75 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %76 = "llvm.insertelement"(%74, %63, %75) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %77 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %78 = "llvm.insertelement"(%76, %63, %77) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %79 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %80 = "llvm.insertelement"(%78, %63, %79) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %81 = "llvm.mlir.constant"() <{value = dense<8796093022207> : vector<8xi64>}> : () -> vector<8xi64>
    %82 = "llvm.mlir.constant"() <{value = dense<[159383552, 159383552, 159383552, 159383552, 1048576, 1048576, 1048576, 1048576]> : vector<8xi64>}> : () -> vector<8xi64>
    %83 = "llvm.mlir.constant"() <{value = dense<1048576> : vector<8xi64>}> : () -> vector<8xi64>
    %84 = "llvm.mlir.constant"() <{value = dense<[8796093022207, 8796093022207, 8796093022207, 8796093022207, 1099511627775, 1099511627775, 1099511627775, 1099511627775]> : vector<8xi64>}> : () -> vector<8xi64>
    %85 = "llvm.mlir.constant"() <{value = dense<[1, 1, 1, 3934839304537, 0, 0, 0, 521695520920]> : vector<8xi64>}> : () -> vector<8xi64>
    %86 = "llvm.mlir.constant"() <{value = dense<[0, 0, 0, 507525298899, 0, 0, 0, 6596238350568]> : vector<8xi64>}> : () -> vector<8xi64>
    %87 = "llvm.mlir.constant"() <{value = dense<[0, 0, 0, 15037786634, 0, 0, 0, 309467527341]> : vector<8xi64>}> : () -> vector<8xi64>
    %88 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %89 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %90 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %91 = "llvm.load"(%arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %92 = "llvm.shufflevector"(%91, %1) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %93 = "llvm.getelementptr"(%arg0, %2) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %94 = "llvm.load"(%93) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %95 = "llvm.shufflevector"(%94, %1) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %96 = "llvm.getelementptr"(%arg0, %2) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 2>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %97 = "llvm.load"(%96) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %98 = "llvm.shufflevector"(%97, %1) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %99 = "llvm.sub"(%92, %91) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %100 = "llvm.add"(%99, %23) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %101 = "llvm.shufflevector"(%100, %92) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %102 = "llvm.sub"(%95, %94) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %103 = "llvm.add"(%102, %40) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %104 = "llvm.shufflevector"(%103, %95) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %105 = "llvm.sub"(%98, %97) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %106 = "llvm.add"(%105, %58) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %107 = "llvm.shufflevector"(%106, %98) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %108 = "llvm.add"(%101, %91) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %109 = "llvm.shufflevector"(%101, %108) <{mask = array<i32: 0, 9, 2, 3, 4, 13, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %110 = "llvm.add"(%104, %94) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %111 = "llvm.shufflevector"(%104, %110) <{mask = array<i32: 0, 9, 2, 3, 4, 13, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %112 = "llvm.add"(%107, %97) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %113 = "llvm.shufflevector"(%107, %112) <{mask = array<i32: 0, 9, 2, 3, 4, 13, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %114 = "llvm.add"(%109, %59) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %115 = "llvm.add"(%111, %60) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %116 = "llvm.add"(%113, %60) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %117 = "llvm.ashr"(%114, %61) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %118 = "llvm.ashr"(%115, %61) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %119 = "llvm.ashr"(%116, %62) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %120 = "llvm.mul"(%119, %80) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %121 = "llvm.and"(%114, %81) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %122 = "llvm.shufflevector"(%120, %119) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %123 = "llvm.add"(%121, %82) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %124 = "llvm.add"(%123, %122) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %125 = "llvm.and"(%115, %81) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %126 = "llvm.add"(%117, %83) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %127 = "llvm.add"(%126, %125) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %128 = "llvm.and"(%116, %84) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %129 = "llvm.add"(%118, %83) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %130 = "llvm.add"(%129, %128) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%88) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%89) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%90) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%88, %89, %90, %124, %127, %130, %85, %86, %87) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_quad_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
    %131 = "llvm.load"(%88) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %132 = "llvm.load"(%89) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %133 = "llvm.load"(%90) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%90) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%89) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%88) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %134 = "llvm.lshr"(%131, %61) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %135 = "llvm.lshr"(%132, %61) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %136 = "llvm.lshr"(%133, %62) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %137 = "llvm.mul"(%136, %80) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %138 = "llvm.and"(%131, %81) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %139 = "llvm.shufflevector"(%137, %136) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %140 = "llvm.add"(%139, %138) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%140, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %141 = "llvm.and"(%132, %81) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %142 = "llvm.add"(%141, %134) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%142, %93) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %143 = "llvm.and"(%133, %84) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %144 = "llvm.add"(%143, %135) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%144, %96) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

def fd_curve25519_into_precomputed : Cfg (Ctxt.ofList [SLLVM.Ty.ptr]) [] :=
  [sllvm_cfg_of| fd_curve25519_into_precomputed_region with
    @fd_r43x6_quad_mul_fast := fd_r43x6_quad_mul_fast]

end Firedancer.Avx512

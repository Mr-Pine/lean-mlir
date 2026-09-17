/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/avx512/region/fd_curve25519_into_precomputed.mlir
module

public import SSA.Projects.SLLVM.Cfg
public import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_quad_mul_fast
-- callee bindings are evaluated while elaborating
public meta import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_quad_mul_fast

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_curve25519_into_precomputed_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = dense<[0, 0, 0, 15037786634, 0, 0, 0, 309467527341]> : vector<8xi64>}> : () -> vector<8xi64>
    %1 = "llvm.mlir.constant"() <{value = dense<[0, 0, 0, 507525298899, 0, 0, 0, 6596238350568]> : vector<8xi64>}> : () -> vector<8xi64>
    %2 = "llvm.mlir.constant"() <{value = dense<[1, 1, 1, 3934839304537, 0, 0, 0, 521695520920]> : vector<8xi64>}> : () -> vector<8xi64>
    %3 = "llvm.mlir.constant"() <{value = dense<[8796093022207, 8796093022207, 8796093022207, 8796093022207, 1099511627775, 1099511627775, 1099511627775, 1099511627775]> : vector<8xi64>}> : () -> vector<8xi64>
    %4 = "llvm.mlir.constant"() <{value = dense<1048576> : vector<8xi64>}> : () -> vector<8xi64>
    %5 = "llvm.mlir.constant"() <{value = dense<[159383552, 159383552, 159383552, 159383552, 1048576, 1048576, 1048576, 1048576]> : vector<8xi64>}> : () -> vector<8xi64>
    %6 = "llvm.mlir.constant"() <{value = dense<8796093022207> : vector<8xi64>}> : () -> vector<8xi64>
    %7 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = dense<[43, 43, 43, 43, 40, 40, 40, 40]> : vector<8xi64>}> : () -> vector<8xi64>
    %9 = "llvm.mlir.constant"() <{value = dense<43> : vector<8xi64>}> : () -> vector<8xi64>
    %10 = "llvm.mlir.constant"() <{value = dense<-1048576> : vector<8xi64>}> : () -> vector<8xi64>
    %11 = "llvm.mlir.constant"() <{value = dense<[-159383552, -159383552, -159383552, -159383552, -1048576, -1048576, -1048576, -1048576]> : vector<8xi64>}> : () -> vector<8xi64>
    %12 = "llvm.mlir.constant"() <{value = 1099511627775 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %14 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %15 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %16 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %17 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %18 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %19 = "llvm.mlir.constant"() <{value = 8796093022189 : i64}> : () -> i64
    %20 = "llvm.mlir.constant"() <{value = 8796093022207 : i64}> : () -> i64
    %21 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %22 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %23 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %24 = "llvm.mlir.poison"() : () -> i64
    %25 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %26 = "llvm.insertelement"(%25, %19, %18) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %27 = "llvm.insertelement"(%26, %24, %22) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %28 = "llvm.insertelement"(%27, %24, %21) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %29 = "llvm.insertelement"(%28, %24, %17) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %30 = "llvm.insertelement"(%29, %20, %16) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %31 = "llvm.insertelement"(%30, %24, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %32 = "llvm.insertelement"(%31, %24, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %33 = "llvm.insertelement"(%32, %24, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %34 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %35 = "llvm.insertelement"(%34, %20, %18) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %36 = "llvm.insertelement"(%35, %24, %22) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %37 = "llvm.insertelement"(%36, %24, %21) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %38 = "llvm.insertelement"(%37, %24, %17) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %39 = "llvm.insertelement"(%38, %20, %16) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %40 = "llvm.insertelement"(%39, %24, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %41 = "llvm.insertelement"(%40, %24, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %42 = "llvm.insertelement"(%41, %24, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %43 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %44 = "llvm.insertelement"(%43, %20, %18) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %45 = "llvm.insertelement"(%44, %24, %22) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %46 = "llvm.insertelement"(%45, %24, %21) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %47 = "llvm.insertelement"(%46, %24, %17) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %48 = "llvm.insertelement"(%47, %12, %16) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %49 = "llvm.insertelement"(%48, %24, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %50 = "llvm.insertelement"(%49, %24, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %51 = "llvm.insertelement"(%50, %24, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %52 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %53 = "llvm.insertelement"(%52, %24, %18) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %54 = "llvm.insertelement"(%53, %24, %22) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %55 = "llvm.insertelement"(%54, %24, %21) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %56 = "llvm.insertelement"(%55, %24, %17) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %57 = "llvm.insertelement"(%56, %7, %16) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %58 = "llvm.insertelement"(%57, %7, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %59 = "llvm.insertelement"(%58, %7, %14) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %60 = "llvm.insertelement"(%59, %7, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %61 = "llvm.alloca"(%22) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %62 = "llvm.alloca"(%22) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %63 = "llvm.alloca"(%22) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %64 = "llvm.load"(%arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %65 = "llvm.shufflevector"(%64, %23) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %66 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    %67 = "llvm.load"(%66) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %68 = "llvm.shufflevector"(%67, %23) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %69 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: 0, 2>}> : (!llvm.ptr) -> !llvm.ptr
    %70 = "llvm.load"(%69) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %71 = "llvm.shufflevector"(%70, %23) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %72 = "llvm.sub"(%65, %64) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %73 = "llvm.add"(%72, %33) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %74 = "llvm.shufflevector"(%73, %65) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %75 = "llvm.sub"(%68, %67) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %76 = "llvm.add"(%75, %42) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %77 = "llvm.shufflevector"(%76, %68) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %78 = "llvm.sub"(%71, %70) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %79 = "llvm.add"(%78, %51) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %80 = "llvm.shufflevector"(%79, %71) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %81 = "llvm.add"(%74, %64) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %82 = "llvm.shufflevector"(%74, %81) <{mask = array<i32: 0, 9, 2, 3, 4, 13, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %83 = "llvm.add"(%77, %67) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %84 = "llvm.shufflevector"(%77, %83) <{mask = array<i32: 0, 9, 2, 3, 4, 13, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %85 = "llvm.add"(%80, %70) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %86 = "llvm.shufflevector"(%80, %85) <{mask = array<i32: 0, 9, 2, 3, 4, 13, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %87 = "llvm.add"(%82, %11) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %88 = "llvm.add"(%84, %10) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %89 = "llvm.add"(%86, %10) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %90 = "llvm.ashr"(%87, %9) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %91 = "llvm.ashr"(%88, %9) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %92 = "llvm.ashr"(%89, %8) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %93 = "llvm.mul"(%92, %60) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %94 = "llvm.and"(%87, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %95 = "llvm.shufflevector"(%93, %92) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %96 = "llvm.add"(%94, %5) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %97 = "llvm.add"(%96, %95) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %98 = "llvm.and"(%88, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %99 = "llvm.add"(%90, %4) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %100 = "llvm.add"(%99, %98) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %101 = "llvm.and"(%89, %3) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %102 = "llvm.add"(%91, %4) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %103 = "llvm.add"(%102, %101) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%61) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%62) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%63) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%61, %62, %63, %97, %100, %103, %2, %1, %0) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_quad_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
    %104 = "llvm.load"(%61) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %105 = "llvm.load"(%62) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %106 = "llvm.load"(%63) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%63) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%62) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%61) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %107 = "llvm.lshr"(%104, %9) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %108 = "llvm.lshr"(%105, %9) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %109 = "llvm.lshr"(%106, %8) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %110 = "llvm.mul"(%109, %60) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %111 = "llvm.and"(%104, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %112 = "llvm.shufflevector"(%110, %109) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %113 = "llvm.add"(%112, %111) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%113, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %114 = "llvm.and"(%105, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %115 = "llvm.add"(%114, %107) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%115, %66) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %116 = "llvm.and"(%106, %3) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %117 = "llvm.add"(%116, %108) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%117, %69) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

sllvm_cfg_def fd_curve25519_into_precomputed : Cfg (Ctxt.ofList [SLLVM.Ty.ptr]) [] :=
  [sllvm_cfg_of| fd_curve25519_into_precomputed_region with
    @fd_r43x6_quad_mul_fast := fd_r43x6_quad_mul_fast]

end Firedancer.Avx512

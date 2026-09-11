/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_quad_mul_fast

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_ed25519_point_add_with_opts_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr, %arg3: i32):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %2 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %4 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %5 = "llvm.mlir.poison"() : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 8796093022207 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 8796093022189 : i64}> : () -> i64
    %8 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %9 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %10 = "llvm.insertelement"(%8, %7, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %11 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %12 = "llvm.insertelement"(%10, %5, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %13 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %14 = "llvm.insertelement"(%12, %5, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %15 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %16 = "llvm.insertelement"(%14, %5, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %17 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %18 = "llvm.insertelement"(%16, %6, %17) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %19 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %20 = "llvm.insertelement"(%18, %5, %19) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %21 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %22 = "llvm.insertelement"(%20, %5, %21) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %23 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %24 = "llvm.insertelement"(%22, %5, %23) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %25 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %26 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %27 = "llvm.insertelement"(%25, %6, %26) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %28 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %29 = "llvm.insertelement"(%27, %5, %28) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %30 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %31 = "llvm.insertelement"(%29, %5, %30) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %32 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %33 = "llvm.insertelement"(%31, %5, %32) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %34 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %35 = "llvm.insertelement"(%33, %6, %34) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %36 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %37 = "llvm.insertelement"(%35, %5, %36) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %38 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %39 = "llvm.insertelement"(%37, %5, %38) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %40 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %41 = "llvm.insertelement"(%39, %5, %40) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %42 = "llvm.mlir.constant"() <{value = 1099511627775 : i64}> : () -> i64
    %43 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %44 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %45 = "llvm.insertelement"(%43, %6, %44) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %46 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %47 = "llvm.insertelement"(%45, %5, %46) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %48 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %49 = "llvm.insertelement"(%47, %5, %48) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %50 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %51 = "llvm.insertelement"(%49, %5, %50) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %52 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %53 = "llvm.insertelement"(%51, %42, %52) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %54 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %55 = "llvm.insertelement"(%53, %5, %54) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %56 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %57 = "llvm.insertelement"(%55, %5, %56) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %58 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %59 = "llvm.insertelement"(%57, %5, %58) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %60 = "llvm.mlir.constant"() <{value = dense<[-159383552, -159383552, -159383552, -159383552, -1048576, -1048576, -1048576, -1048576]> : vector<8xi64>}> : () -> vector<8xi64>
    %61 = "llvm.mlir.constant"() <{value = dense<-1048576> : vector<8xi64>}> : () -> vector<8xi64>
    %62 = "llvm.mlir.constant"() <{value = dense<43> : vector<8xi64>}> : () -> vector<8xi64>
    %63 = "llvm.mlir.constant"() <{value = dense<[43, 43, 43, 43, 40, 40, 40, 40]> : vector<8xi64>}> : () -> vector<8xi64>
    %64 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %65 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %66 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %67 = "llvm.insertelement"(%65, %5, %66) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %68 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %69 = "llvm.insertelement"(%67, %5, %68) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %70 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %71 = "llvm.insertelement"(%69, %5, %70) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %72 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %73 = "llvm.insertelement"(%71, %5, %72) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %74 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %75 = "llvm.insertelement"(%73, %64, %74) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %76 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %77 = "llvm.insertelement"(%75, %64, %76) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %78 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %79 = "llvm.insertelement"(%77, %64, %78) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %80 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %81 = "llvm.insertelement"(%79, %64, %80) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %82 = "llvm.mlir.constant"() <{value = dense<8796093022207> : vector<8xi64>}> : () -> vector<8xi64>
    %83 = "llvm.mlir.constant"() <{value = dense<[159383552, 159383552, 159383552, 159383552, 1048576, 1048576, 1048576, 1048576]> : vector<8xi64>}> : () -> vector<8xi64>
    %84 = "llvm.mlir.constant"() <{value = dense<1048576> : vector<8xi64>}> : () -> vector<8xi64>
    %85 = "llvm.mlir.constant"() <{value = dense<[8796093022207, 8796093022207, 8796093022207, 8796093022207, 1099511627775, 1099511627775, 1099511627775, 1099511627775]> : vector<8xi64>}> : () -> vector<8xi64>
    %86 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %87 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %88 = "llvm.insertelement"(%86, %7, %87) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %89 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %90 = "llvm.insertelement"(%88, %5, %89) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %91 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %92 = "llvm.insertelement"(%90, %5, %91) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %93 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %94 = "llvm.insertelement"(%92, %7, %93) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %95 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %96 = "llvm.insertelement"(%94, %6, %95) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %97 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %98 = "llvm.insertelement"(%96, %5, %97) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %99 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %100 = "llvm.insertelement"(%98, %5, %99) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %101 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %102 = "llvm.insertelement"(%100, %6, %101) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %103 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %104 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %105 = "llvm.insertelement"(%103, %6, %104) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %106 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %107 = "llvm.insertelement"(%105, %5, %106) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %108 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %109 = "llvm.insertelement"(%107, %5, %108) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %110 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %111 = "llvm.insertelement"(%109, %6, %110) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %112 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %113 = "llvm.insertelement"(%111, %6, %112) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %114 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %115 = "llvm.insertelement"(%113, %5, %114) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %116 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %117 = "llvm.insertelement"(%115, %5, %116) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %118 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %119 = "llvm.insertelement"(%117, %6, %118) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %120 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %121 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %122 = "llvm.insertelement"(%120, %6, %121) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %123 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %124 = "llvm.insertelement"(%122, %5, %123) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %125 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %126 = "llvm.insertelement"(%124, %5, %125) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %127 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %128 = "llvm.insertelement"(%126, %6, %127) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %129 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %130 = "llvm.insertelement"(%128, %42, %129) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %131 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %132 = "llvm.insertelement"(%130, %5, %131) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %133 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %134 = "llvm.insertelement"(%132, %5, %133) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %135 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %136 = "llvm.insertelement"(%134, %42, %135) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %137 = "llvm.mlir.constant"() <{value = dense<[1, 1, 1, 3934839304537, 0, 0, 0, 521695520920]> : vector<8xi64>}> : () -> vector<8xi64>
    %138 = "llvm.mlir.constant"() <{value = dense<[0, 0, 0, 507525298899, 0, 0, 0, 6596238350568]> : vector<8xi64>}> : () -> vector<8xi64>
    %139 = "llvm.mlir.constant"() <{value = dense<[0, 0, 0, 15037786634, 0, 0, 0, 309467527341]> : vector<8xi64>}> : () -> vector<8xi64>
    %140 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %141 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %142 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %143 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %144 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %145 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %146 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %147 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %148 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %149 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %150 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %151 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %152 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %153 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %154 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %155 = "llvm.icmp"(%arg3, %1) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%155)[^bb2, ^bb1] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:  // pred: ^bb0
    %156 = "llvm.load"(%arg2) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %157 = "llvm.getelementptr"(%arg2, %2) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %158 = "llvm.load"(%157) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %159 = "llvm.getelementptr"(%arg2, %2) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 2>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %160 = "llvm.load"(%159) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %161 = "llvm.load"(%arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %162 = "llvm.shufflevector"(%161, %4) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %163 = "llvm.getelementptr"(%arg1, %2) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %164 = "llvm.load"(%163) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %165 = "llvm.shufflevector"(%164, %4) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %166 = "llvm.getelementptr"(%arg1, %2) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 2>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %167 = "llvm.load"(%166) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %168 = "llvm.shufflevector"(%167, %4) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %169 = "llvm.sub"(%162, %161) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %170 = "llvm.add"(%169, %24) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %171 = "llvm.shufflevector"(%170, %162) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %172 = "llvm.sub"(%165, %164) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %173 = "llvm.add"(%172, %41) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %174 = "llvm.shufflevector"(%173, %165) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %175 = "llvm.sub"(%168, %167) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %176 = "llvm.add"(%175, %59) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %177 = "llvm.shufflevector"(%176, %168) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %178 = "llvm.add"(%171, %161) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %179 = "llvm.shufflevector"(%171, %178) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %180 = "llvm.add"(%174, %164) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %181 = "llvm.shufflevector"(%174, %180) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %182 = "llvm.add"(%177, %167) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %183 = "llvm.shufflevector"(%177, %182) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %184 = "llvm.add"(%179, %60) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %185 = "llvm.add"(%181, %61) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %186 = "llvm.add"(%183, %61) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %187 = "llvm.ashr"(%184, %62) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %188 = "llvm.ashr"(%185, %62) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %189 = "llvm.ashr"(%186, %63) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %190 = "llvm.mul"(%189, %81) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %191 = "llvm.and"(%184, %82) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %192 = "llvm.shufflevector"(%190, %189) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %193 = "llvm.add"(%191, %83) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %194 = "llvm.add"(%193, %192) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %195 = "llvm.and"(%185, %82) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %196 = "llvm.add"(%187, %84) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %197 = "llvm.add"(%196, %195) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %198 = "llvm.and"(%186, %85) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %199 = "llvm.add"(%188, %84) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %200 = "llvm.add"(%199, %198) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%140) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%141) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%142) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%140, %141, %142, %156, %158, %160, %194, %197, %200) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_quad_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
    %201 = "llvm.load"(%140) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %202 = "llvm.load"(%141) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %203 = "llvm.load"(%142) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%142) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%141) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%140) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %204 = "llvm.lshr"(%201, %62) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %205 = "llvm.lshr"(%202, %62) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %206 = "llvm.lshr"(%203, %63) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %207 = "llvm.mul"(%206, %81) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %208 = "llvm.and"(%201, %82) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %209 = "llvm.shufflevector"(%207, %206) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %210 = "llvm.add"(%209, %208) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %211 = "llvm.and"(%202, %82) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %212 = "llvm.add"(%211, %204) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %213 = "llvm.and"(%203, %85) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %214 = "llvm.add"(%213, %205) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %215 = "llvm.shufflevector"(%210, %4) <{mask = array<i32: 1, 0, 3, 2, 5, 4, 7, 6>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %216 = "llvm.shufflevector"(%212, %4) <{mask = array<i32: 1, 0, 3, 2, 5, 4, 7, 6>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %217 = "llvm.shufflevector"(%214, %4) <{mask = array<i32: 1, 0, 3, 2, 5, 4, 7, 6>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %218 = "llvm.sub"(%215, %210) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %219 = "llvm.add"(%218, %102) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %220 = "llvm.shufflevector"(%219, %215) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %221 = "llvm.sub"(%216, %212) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %222 = "llvm.add"(%221, %119) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %223 = "llvm.shufflevector"(%222, %216) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %224 = "llvm.sub"(%217, %214) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %225 = "llvm.add"(%224, %136) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %226 = "llvm.shufflevector"(%225, %217) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %227 = "llvm.add"(%220, %210) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %228 = "llvm.shufflevector"(%220, %227) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %229 = "llvm.add"(%223, %212) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %230 = "llvm.shufflevector"(%223, %229) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %231 = "llvm.add"(%226, %214) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %232 = "llvm.shufflevector"(%226, %231) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %233 = "llvm.add"(%228, %60) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %234 = "llvm.add"(%230, %61) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %235 = "llvm.add"(%232, %61) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %236 = "llvm.ashr"(%233, %62) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %237 = "llvm.ashr"(%234, %62) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %238 = "llvm.ashr"(%235, %63) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %239 = "llvm.mul"(%238, %81) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %240 = "llvm.and"(%233, %82) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %241 = "llvm.shufflevector"(%239, %238) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %242 = "llvm.add"(%241, %83) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %243 = "llvm.add"(%242, %240) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %244 = "llvm.and"(%234, %82) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %245 = "llvm.add"(%244, %84) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %246 = "llvm.add"(%245, %236) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %247 = "llvm.and"(%235, %85) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %248 = "llvm.add"(%237, %84) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %249 = "llvm.add"(%248, %247) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %250 = "llvm.shufflevector"(%243, %4) <{mask = array<i32: 0, 2, 2, 0, 4, 6, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %251 = "llvm.shufflevector"(%246, %4) <{mask = array<i32: 0, 2, 2, 0, 4, 6, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %252 = "llvm.shufflevector"(%249, %4) <{mask = array<i32: 0, 2, 2, 0, 4, 6, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %253 = "llvm.shufflevector"(%243, %4) <{mask = array<i32: 3, 1, 3, 1, 7, 5, 7, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %254 = "llvm.shufflevector"(%246, %4) <{mask = array<i32: 3, 1, 3, 1, 7, 5, 7, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %255 = "llvm.shufflevector"(%249, %4) <{mask = array<i32: 3, 1, 3, 1, 7, 5, 7, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%143) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%144) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%145) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%143, %144, %145, %250, %251, %252, %253, %254, %255) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_quad_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
    %256 = "llvm.load"(%143) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %257 = "llvm.load"(%144) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %258 = "llvm.load"(%145) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%145) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%144) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%143) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.br"(%256, %257, %258)[^bb3] : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
  ^bb2:  // pred: ^bb0
    %259 = "llvm.load"(%arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %260 = "llvm.shufflevector"(%259, %4) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %261 = "llvm.getelementptr"(%arg1, %2) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %262 = "llvm.load"(%261) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %263 = "llvm.shufflevector"(%262, %4) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %264 = "llvm.getelementptr"(%arg1, %2) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 2>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %265 = "llvm.load"(%264) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %266 = "llvm.shufflevector"(%265, %4) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %267 = "llvm.load"(%arg2) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %268 = "llvm.shufflevector"(%267, %4) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %269 = "llvm.getelementptr"(%arg2, %2) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %270 = "llvm.load"(%269) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %271 = "llvm.shufflevector"(%270, %4) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %272 = "llvm.getelementptr"(%arg2, %2) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 2>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %273 = "llvm.load"(%272) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %274 = "llvm.shufflevector"(%273, %4) <{mask = array<i32: 1, 0, 2, 3, 5, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %275 = "llvm.sub"(%260, %259) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %276 = "llvm.add"(%275, %24) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %277 = "llvm.shufflevector"(%276, %260) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %278 = "llvm.sub"(%263, %262) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %279 = "llvm.add"(%278, %41) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %280 = "llvm.shufflevector"(%279, %263) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %281 = "llvm.sub"(%266, %265) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %282 = "llvm.add"(%281, %59) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %283 = "llvm.shufflevector"(%282, %266) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %284 = "llvm.sub"(%268, %267) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %285 = "llvm.add"(%284, %24) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %286 = "llvm.shufflevector"(%285, %268) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %287 = "llvm.sub"(%271, %270) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %288 = "llvm.add"(%287, %41) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %289 = "llvm.shufflevector"(%288, %271) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %290 = "llvm.sub"(%274, %273) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %291 = "llvm.add"(%290, %59) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %292 = "llvm.shufflevector"(%291, %274) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %293 = "llvm.add"(%277, %259) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %294 = "llvm.shufflevector"(%277, %293) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %295 = "llvm.add"(%280, %262) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %296 = "llvm.shufflevector"(%280, %295) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %297 = "llvm.add"(%283, %265) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %298 = "llvm.shufflevector"(%283, %297) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %299 = "llvm.add"(%286, %267) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %300 = "llvm.shufflevector"(%286, %299) <{mask = array<i32: 0, 9, 2, 3, 4, 13, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %301 = "llvm.add"(%289, %270) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %302 = "llvm.shufflevector"(%289, %301) <{mask = array<i32: 0, 9, 2, 3, 4, 13, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %303 = "llvm.add"(%292, %273) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %304 = "llvm.shufflevector"(%292, %303) <{mask = array<i32: 0, 9, 2, 3, 4, 13, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %305 = "llvm.add"(%294, %60) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %306 = "llvm.add"(%296, %61) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %307 = "llvm.add"(%298, %61) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %308 = "llvm.ashr"(%305, %62) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %309 = "llvm.ashr"(%306, %62) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %310 = "llvm.ashr"(%307, %63) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %311 = "llvm.mul"(%310, %81) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %312 = "llvm.and"(%305, %82) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %313 = "llvm.shufflevector"(%311, %310) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %314 = "llvm.add"(%312, %83) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %315 = "llvm.add"(%314, %313) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %316 = "llvm.and"(%306, %82) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %317 = "llvm.add"(%308, %84) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %318 = "llvm.add"(%317, %316) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %319 = "llvm.and"(%307, %85) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %320 = "llvm.add"(%309, %84) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %321 = "llvm.add"(%320, %319) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %322 = "llvm.add"(%300, %60) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %323 = "llvm.add"(%302, %61) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %324 = "llvm.add"(%304, %61) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %325 = "llvm.ashr"(%322, %62) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %326 = "llvm.ashr"(%323, %62) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %327 = "llvm.ashr"(%324, %63) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %328 = "llvm.mul"(%327, %81) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %329 = "llvm.and"(%322, %82) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %330 = "llvm.shufflevector"(%328, %327) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %331 = "llvm.add"(%329, %83) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %332 = "llvm.add"(%331, %330) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %333 = "llvm.and"(%323, %82) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %334 = "llvm.add"(%325, %84) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %335 = "llvm.add"(%334, %333) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %336 = "llvm.and"(%324, %85) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %337 = "llvm.add"(%326, %84) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %338 = "llvm.add"(%337, %336) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%146) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%147) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%148) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%146, %147, %148, %315, %318, %321, %137, %138, %139) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_quad_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
    %339 = "llvm.load"(%146) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %340 = "llvm.load"(%147) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %341 = "llvm.load"(%148) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%148) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%147) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%146) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %342 = "llvm.lshr"(%339, %62) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %343 = "llvm.lshr"(%340, %62) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %344 = "llvm.lshr"(%341, %63) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %345 = "llvm.mul"(%344, %81) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %346 = "llvm.and"(%339, %82) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %347 = "llvm.shufflevector"(%345, %344) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %348 = "llvm.add"(%347, %346) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %349 = "llvm.and"(%340, %82) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %350 = "llvm.add"(%349, %342) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %351 = "llvm.and"(%341, %85) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %352 = "llvm.add"(%351, %343) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%149) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%150) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%151) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%149, %150, %151, %348, %350, %352, %332, %335, %338) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_quad_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
    %353 = "llvm.load"(%149) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %354 = "llvm.load"(%150) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %355 = "llvm.load"(%151) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%151) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%150) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%149) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %356 = "llvm.shufflevector"(%353, %4) <{mask = array<i32: 1, 0, 3, 2, 5, 4, 7, 6>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %357 = "llvm.shufflevector"(%354, %4) <{mask = array<i32: 1, 0, 3, 2, 5, 4, 7, 6>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %358 = "llvm.shufflevector"(%355, %4) <{mask = array<i32: 1, 0, 3, 2, 5, 4, 7, 6>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %359 = "llvm.sub"(%356, %353) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %360 = "llvm.add"(%359, %102) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %361 = "llvm.shufflevector"(%360, %356) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %362 = "llvm.sub"(%357, %354) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %363 = "llvm.add"(%362, %119) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %364 = "llvm.shufflevector"(%363, %357) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %365 = "llvm.sub"(%358, %355) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %366 = "llvm.add"(%365, %136) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %367 = "llvm.shufflevector"(%366, %358) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %368 = "llvm.add"(%361, %353) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %369 = "llvm.shufflevector"(%361, %368) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %370 = "llvm.add"(%364, %354) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %371 = "llvm.shufflevector"(%364, %370) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %372 = "llvm.add"(%367, %355) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %373 = "llvm.shufflevector"(%367, %372) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %374 = "llvm.add"(%369, %60) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %375 = "llvm.add"(%371, %61) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %376 = "llvm.add"(%373, %61) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %377 = "llvm.ashr"(%374, %62) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %378 = "llvm.ashr"(%375, %62) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %379 = "llvm.ashr"(%376, %63) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %380 = "llvm.mul"(%379, %81) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %381 = "llvm.and"(%374, %82) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %382 = "llvm.shufflevector"(%380, %379) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %383 = "llvm.add"(%381, %83) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %384 = "llvm.add"(%383, %382) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %385 = "llvm.and"(%375, %82) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %386 = "llvm.add"(%377, %84) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %387 = "llvm.add"(%386, %385) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %388 = "llvm.and"(%376, %85) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %389 = "llvm.add"(%378, %84) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %390 = "llvm.add"(%389, %388) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %391 = "llvm.shufflevector"(%384, %4) <{mask = array<i32: 0, 2, 2, 0, 4, 6, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %392 = "llvm.shufflevector"(%387, %4) <{mask = array<i32: 0, 2, 2, 0, 4, 6, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %393 = "llvm.shufflevector"(%390, %4) <{mask = array<i32: 0, 2, 2, 0, 4, 6, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %394 = "llvm.shufflevector"(%384, %4) <{mask = array<i32: 3, 1, 3, 1, 7, 5, 7, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %395 = "llvm.shufflevector"(%387, %4) <{mask = array<i32: 3, 1, 3, 1, 7, 5, 7, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %396 = "llvm.shufflevector"(%390, %4) <{mask = array<i32: 3, 1, 3, 1, 7, 5, 7, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%152) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%153) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%154) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%152, %153, %154, %391, %392, %393, %394, %395, %396) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_quad_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
    %397 = "llvm.load"(%152) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %398 = "llvm.load"(%153) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %399 = "llvm.load"(%154) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%154) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%153) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%152) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.br"(%397, %398, %399)[^bb3] : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
  ^bb3(%400: vector<8xi64>, %401: vector<8xi64>, %402: vector<8xi64>):  // 2 preds: ^bb1, ^bb2
    %403 = "llvm.lshr"(%400, %62) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %404 = "llvm.lshr"(%401, %62) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %405 = "llvm.lshr"(%402, %63) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %406 = "llvm.mul"(%405, %81) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %407 = "llvm.and"(%400, %82) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %408 = "llvm.shufflevector"(%406, %405) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %409 = "llvm.add"(%408, %407) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%409, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %410 = "llvm.and"(%401, %82) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %411 = "llvm.add"(%410, %403) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %412 = "llvm.getelementptr"(%arg0, %2) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%411, %412) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %413 = "llvm.and"(%402, %85) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %414 = "llvm.add"(%413, %404) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %415 = "llvm.getelementptr"(%arg0, %2) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 2>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%414, %415) <{alignment = 64 : i64, ordering = 0 : i64}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

def fd_ed25519_point_add_with_opts :
    Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 32, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr])
      [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_ed25519_point_add_with_opts_region with
    @fd_r43x6_quad_mul_fast := fd_r43x6_quad_mul_fast]

end Firedancer.Avx512

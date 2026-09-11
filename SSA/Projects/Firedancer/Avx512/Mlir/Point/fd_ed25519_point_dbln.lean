/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_quad_sqr_fast
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_quad_mul_fast

namespace Firedancer.Avx512
open LeanMLIR SLLVM

-- `^bb0` is 264 operations, past the default depth of the region parser.
set_option maxRecDepth 4000 in
def fd_ed25519_point_dbln_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: i32):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %2 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %4 = "llvm.mlir.constant"() <{value = dense<[0, 0, 1, 0, 0, 0, 1, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %5 = "llvm.mlir.poison"() : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 8796093022207 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 8796093022189 : i64}> : () -> i64
    %8 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %9 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %10 = "llvm.insertelement"(%8, %5, %9) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %11 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %12 = "llvm.insertelement"(%10, %7, %11) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %13 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %14 = "llvm.insertelement"(%12, %7, %13) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %15 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %16 = "llvm.insertelement"(%14, %5, %15) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %17 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %18 = "llvm.insertelement"(%16, %5, %17) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %19 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %20 = "llvm.insertelement"(%18, %6, %19) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %21 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %22 = "llvm.insertelement"(%20, %6, %21) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %23 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %24 = "llvm.insertelement"(%22, %5, %23) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %25 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %26 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %27 = "llvm.insertelement"(%25, %5, %26) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %28 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %29 = "llvm.insertelement"(%27, %6, %28) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %30 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %31 = "llvm.insertelement"(%29, %6, %30) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %32 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %33 = "llvm.insertelement"(%31, %5, %32) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %34 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %35 = "llvm.insertelement"(%33, %5, %34) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %36 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %37 = "llvm.insertelement"(%35, %6, %36) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %38 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %39 = "llvm.insertelement"(%37, %6, %38) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %40 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %41 = "llvm.insertelement"(%39, %5, %40) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %42 = "llvm.mlir.constant"() <{value = 1099511627775 : i64}> : () -> i64
    %43 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %44 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %45 = "llvm.insertelement"(%43, %5, %44) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %46 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %47 = "llvm.insertelement"(%45, %6, %46) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %48 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %49 = "llvm.insertelement"(%47, %6, %48) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %50 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %51 = "llvm.insertelement"(%49, %5, %50) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %52 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %53 = "llvm.insertelement"(%51, %5, %52) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %54 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %55 = "llvm.insertelement"(%53, %42, %54) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %56 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %57 = "llvm.insertelement"(%55, %42, %56) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %58 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %59 = "llvm.insertelement"(%57, %5, %58) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %60 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %61 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %62 = "llvm.insertelement"(%60, %7, %61) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %63 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %64 = "llvm.insertelement"(%62, %5, %63) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %65 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %66 = "llvm.insertelement"(%64, %5, %65) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %67 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %68 = "llvm.insertelement"(%66, %5, %67) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %69 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %70 = "llvm.insertelement"(%68, %6, %69) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %71 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %72 = "llvm.insertelement"(%70, %5, %71) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %73 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %74 = "llvm.insertelement"(%72, %5, %73) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %75 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %76 = "llvm.insertelement"(%74, %5, %75) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %77 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %78 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %79 = "llvm.insertelement"(%77, %6, %78) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %80 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %81 = "llvm.insertelement"(%79, %5, %80) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %82 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %83 = "llvm.insertelement"(%81, %5, %82) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %84 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %85 = "llvm.insertelement"(%83, %5, %84) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %86 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %87 = "llvm.insertelement"(%85, %6, %86) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %88 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %89 = "llvm.insertelement"(%87, %5, %88) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %90 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %91 = "llvm.insertelement"(%89, %5, %90) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %92 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %93 = "llvm.insertelement"(%91, %5, %92) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %94 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %95 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %96 = "llvm.insertelement"(%94, %6, %95) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %97 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %98 = "llvm.insertelement"(%96, %5, %97) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %99 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %100 = "llvm.insertelement"(%98, %5, %99) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %101 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %102 = "llvm.insertelement"(%100, %5, %101) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %103 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %104 = "llvm.insertelement"(%102, %42, %103) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %105 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %106 = "llvm.insertelement"(%104, %5, %105) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %107 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %108 = "llvm.insertelement"(%106, %5, %107) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %109 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %110 = "llvm.insertelement"(%108, %5, %109) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %111 = "llvm.mlir.constant"() <{value = dense<[-159383552, -159383552, -159383552, -159383552, -1048576, -1048576, -1048576, -1048576]> : vector<8xi64>}> : () -> vector<8xi64>
    %112 = "llvm.mlir.constant"() <{value = dense<-1048576> : vector<8xi64>}> : () -> vector<8xi64>
    %113 = "llvm.mlir.constant"() <{value = dense<43> : vector<8xi64>}> : () -> vector<8xi64>
    %114 = "llvm.mlir.constant"() <{value = dense<[43, 43, 43, 43, 40, 40, 40, 40]> : vector<8xi64>}> : () -> vector<8xi64>
    %115 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %116 = "llvm.mlir.undef"() : () -> vector<8xi64>
    %117 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %118 = "llvm.insertelement"(%116, %5, %117) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %119 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %120 = "llvm.insertelement"(%118, %5, %119) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %121 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %122 = "llvm.insertelement"(%120, %5, %121) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %123 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %124 = "llvm.insertelement"(%122, %5, %123) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %125 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %126 = "llvm.insertelement"(%124, %115, %125) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %127 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %128 = "llvm.insertelement"(%126, %115, %127) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %129 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %130 = "llvm.insertelement"(%128, %115, %129) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %131 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %132 = "llvm.insertelement"(%130, %115, %131) : (vector<8xi64>, i64, i32) -> vector<8xi64>
    %133 = "llvm.mlir.constant"() <{value = dense<8796093022207> : vector<8xi64>}> : () -> vector<8xi64>
    %134 = "llvm.mlir.constant"() <{value = dense<[159383552, 159383552, 159383552, 159383552, 1048576, 1048576, 1048576, 1048576]> : vector<8xi64>}> : () -> vector<8xi64>
    %135 = "llvm.mlir.constant"() <{value = dense<1048576> : vector<8xi64>}> : () -> vector<8xi64>
    %136 = "llvm.mlir.constant"() <{value = dense<[8796093022207, 8796093022207, 8796093022207, 8796093022207, 1099511627775, 1099511627775, 1099511627775, 1099511627775]> : vector<8xi64>}> : () -> vector<8xi64>
    %137 = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %138 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
    %139 = "llvm.alloca"(%0) <{alignment = 64 : i64, elem_type = vector<8xi64>}> : (i32) -> !llvm.ptr
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
    %150 = "llvm.load"(%arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %151 = "llvm.shufflevector"(%150, %1) <{mask = array<i32: 1, 1, 2, 0, 5, 5, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %152 = "llvm.getelementptr"(%arg1, %2) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %153 = "llvm.load"(%152) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %154 = "llvm.shufflevector"(%153, %1) <{mask = array<i32: 1, 1, 2, 0, 5, 5, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %155 = "llvm.getelementptr"(%arg1, %2) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 2>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %156 = "llvm.load"(%155) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %157 = "llvm.shufflevector"(%156, %1) <{mask = array<i32: 1, 1, 2, 0, 5, 5, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %158 = "llvm.add"(%151, %150) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %159 = "llvm.shufflevector"(%158, %151) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %160 = "llvm.add"(%154, %153) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %161 = "llvm.shufflevector"(%160, %154) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %162 = "llvm.add"(%157, %156) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %163 = "llvm.shufflevector"(%162, %157) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%138) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%139) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%140) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%138, %139, %140, %159, %161, %163) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_quad_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
    %164 = "llvm.load"(%138) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %165 = "llvm.load"(%139) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %166 = "llvm.load"(%140) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%140) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%139) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%138) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %167 = "llvm.shl"(%164, %4) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %168 = "llvm.shl"(%165, %4) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %169 = "llvm.shl"(%166, %4) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %170 = "llvm.shufflevector"(%167, %1) <{mask = array<i32: 3, 3, 3, 3, 7, 7, 7, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %171 = "llvm.shufflevector"(%168, %1) <{mask = array<i32: 3, 3, 3, 3, 7, 7, 7, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %172 = "llvm.shufflevector"(%169, %1) <{mask = array<i32: 3, 3, 3, 3, 7, 7, 7, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %173 = "llvm.shufflevector"(%167, %1) <{mask = array<i32: 1, 1, 1, 1, 5, 5, 5, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %174 = "llvm.shufflevector"(%168, %1) <{mask = array<i32: 1, 1, 1, 1, 5, 5, 5, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %175 = "llvm.shufflevector"(%169, %1) <{mask = array<i32: 1, 1, 1, 1, 5, 5, 5, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %176 = "llvm.add"(%170, %173) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %177 = "llvm.shufflevector"(%176, %170) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %178 = "llvm.add"(%171, %174) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %179 = "llvm.shufflevector"(%178, %171) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %180 = "llvm.add"(%172, %175) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %181 = "llvm.shufflevector"(%180, %172) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %182 = "llvm.sub"(%177, %173) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %183 = "llvm.add"(%182, %24) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %184 = "llvm.shufflevector"(%177, %183) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %185 = "llvm.sub"(%179, %174) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %186 = "llvm.add"(%185, %41) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %187 = "llvm.shufflevector"(%179, %186) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %188 = "llvm.sub"(%181, %175) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %189 = "llvm.add"(%188, %59) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %190 = "llvm.shufflevector"(%181, %189) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %191 = "llvm.add"(%184, %167) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %192 = "llvm.shufflevector"(%184, %191) <{mask = array<i32: 0, 1, 10, 3, 4, 5, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %193 = "llvm.add"(%187, %168) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %194 = "llvm.shufflevector"(%187, %193) <{mask = array<i32: 0, 1, 10, 3, 4, 5, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %195 = "llvm.add"(%190, %169) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %196 = "llvm.shufflevector"(%190, %195) <{mask = array<i32: 0, 1, 10, 3, 4, 5, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %197 = "llvm.sub"(%192, %167) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %198 = "llvm.add"(%197, %76) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %199 = "llvm.shufflevector"(%198, %192) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %200 = "llvm.sub"(%194, %168) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %201 = "llvm.add"(%200, %93) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %202 = "llvm.shufflevector"(%201, %194) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %203 = "llvm.sub"(%196, %169) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %204 = "llvm.add"(%203, %110) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %205 = "llvm.shufflevector"(%204, %196) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %206 = "llvm.add"(%199, %111) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %207 = "llvm.add"(%202, %112) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %208 = "llvm.add"(%205, %112) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %209 = "llvm.ashr"(%206, %113) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %210 = "llvm.ashr"(%207, %113) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %211 = "llvm.ashr"(%208, %114) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %212 = "llvm.mul"(%211, %132) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %213 = "llvm.and"(%206, %133) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %214 = "llvm.shufflevector"(%212, %211) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %215 = "llvm.add"(%213, %134) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %216 = "llvm.add"(%215, %214) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %217 = "llvm.and"(%207, %133) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %218 = "llvm.add"(%209, %135) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %219 = "llvm.add"(%218, %217) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %220 = "llvm.and"(%208, %136) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %221 = "llvm.add"(%210, %135) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %222 = "llvm.add"(%221, %220) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %223 = "llvm.shufflevector"(%216, %1) <{mask = array<i32: 0, 1, 1, 0, 4, 5, 5, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %224 = "llvm.shufflevector"(%219, %1) <{mask = array<i32: 0, 1, 1, 0, 4, 5, 5, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %225 = "llvm.shufflevector"(%222, %1) <{mask = array<i32: 0, 1, 1, 0, 4, 5, 5, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %226 = "llvm.shufflevector"(%216, %1) <{mask = array<i32: 2, 3, 2, 3, 6, 7, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %227 = "llvm.shufflevector"(%219, %1) <{mask = array<i32: 2, 3, 2, 3, 6, 7, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %228 = "llvm.shufflevector"(%222, %1) <{mask = array<i32: 2, 3, 2, 3, 6, 7, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%141) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%142) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%143) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%141, %142, %143, %223, %224, %225, %226, %227, %228) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_quad_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
    %229 = "llvm.load"(%141) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %230 = "llvm.load"(%142) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %231 = "llvm.load"(%143) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%143) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%142) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%141) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %232 = "llvm.lshr"(%229, %113) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %233 = "llvm.lshr"(%230, %113) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %234 = "llvm.lshr"(%231, %114) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %235 = "llvm.mul"(%234, %132) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %236 = "llvm.and"(%229, %133) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %237 = "llvm.shufflevector"(%235, %234) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %238 = "llvm.add"(%237, %236) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%238, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %239 = "llvm.and"(%230, %133) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %240 = "llvm.add"(%239, %232) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %241 = "llvm.getelementptr"(%arg0, %2) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%240, %241) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %242 = "llvm.and"(%231, %136) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %243 = "llvm.add"(%242, %233) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %244 = "llvm.getelementptr"(%arg0, %2) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 2>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%243, %244) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    %245 = "llvm.icmp"(%arg2, %0) <{predicate = 4 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%245, %243, %240, %238, %137)[^bb3, ^bb2] <{operandSegmentSizes = array<i32: 1, 4, 0>}> : (i1, vector<8xi64>, vector<8xi64>, vector<8xi64>, i8) -> ()
  ^bb1:  // pred: ^bb3
    "llvm.store"(%333, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%335, %241) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%337, %244) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.br"()[^bb2] : () -> ()
  ^bb2:  // 2 preds: ^bb0, ^bb1
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
  ^bb3(%246: vector<8xi64>, %247: vector<8xi64>, %248: vector<8xi64>, %249: i8):  // 2 preds: ^bb0, ^bb3
    %250 = "llvm.shufflevector"(%248, %1) <{mask = array<i32: 1, 1, 2, 0, 5, 5, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %251 = "llvm.shufflevector"(%247, %1) <{mask = array<i32: 1, 1, 2, 0, 5, 5, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %252 = "llvm.shufflevector"(%246, %1) <{mask = array<i32: 1, 1, 2, 0, 5, 5, 6, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %253 = "llvm.add"(%250, %248) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %254 = "llvm.shufflevector"(%253, %250) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %255 = "llvm.add"(%251, %247) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %256 = "llvm.shufflevector"(%255, %251) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %257 = "llvm.add"(%252, %246) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %258 = "llvm.shufflevector"(%257, %252) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%144) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%145) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%146) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%144, %145, %146, %254, %256, %258) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_quad_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
    %259 = "llvm.load"(%144) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %260 = "llvm.load"(%145) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %261 = "llvm.load"(%146) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%146) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%145) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%144) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %262 = "llvm.shl"(%259, %4) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %263 = "llvm.shl"(%260, %4) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %264 = "llvm.shl"(%261, %4) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %265 = "llvm.shufflevector"(%262, %1) <{mask = array<i32: 3, 3, 3, 3, 7, 7, 7, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %266 = "llvm.shufflevector"(%263, %1) <{mask = array<i32: 3, 3, 3, 3, 7, 7, 7, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %267 = "llvm.shufflevector"(%264, %1) <{mask = array<i32: 3, 3, 3, 3, 7, 7, 7, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %268 = "llvm.shufflevector"(%262, %1) <{mask = array<i32: 1, 1, 1, 1, 5, 5, 5, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %269 = "llvm.shufflevector"(%263, %1) <{mask = array<i32: 1, 1, 1, 1, 5, 5, 5, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %270 = "llvm.shufflevector"(%264, %1) <{mask = array<i32: 1, 1, 1, 1, 5, 5, 5, 5>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %271 = "llvm.add"(%265, %268) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %272 = "llvm.shufflevector"(%271, %265) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %273 = "llvm.add"(%266, %269) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %274 = "llvm.shufflevector"(%273, %266) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %275 = "llvm.add"(%267, %270) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %276 = "llvm.shufflevector"(%275, %267) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %277 = "llvm.sub"(%272, %268) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %278 = "llvm.add"(%277, %24) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %279 = "llvm.shufflevector"(%272, %278) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %280 = "llvm.sub"(%274, %269) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %281 = "llvm.add"(%280, %41) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %282 = "llvm.shufflevector"(%274, %281) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %283 = "llvm.sub"(%276, %270) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %284 = "llvm.add"(%283, %59) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %285 = "llvm.shufflevector"(%276, %284) <{mask = array<i32: 0, 9, 10, 3, 4, 13, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %286 = "llvm.add"(%279, %262) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %287 = "llvm.shufflevector"(%279, %286) <{mask = array<i32: 0, 1, 10, 3, 4, 5, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %288 = "llvm.add"(%282, %263) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %289 = "llvm.shufflevector"(%282, %288) <{mask = array<i32: 0, 1, 10, 3, 4, 5, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %290 = "llvm.add"(%285, %264) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %291 = "llvm.shufflevector"(%285, %290) <{mask = array<i32: 0, 1, 10, 3, 4, 5, 14, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %292 = "llvm.sub"(%287, %262) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %293 = "llvm.add"(%292, %76) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %294 = "llvm.shufflevector"(%293, %287) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %295 = "llvm.sub"(%289, %263) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %296 = "llvm.add"(%295, %93) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %297 = "llvm.shufflevector"(%296, %289) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %298 = "llvm.sub"(%291, %264) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %299 = "llvm.add"(%298, %110) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %300 = "llvm.shufflevector"(%299, %291) <{mask = array<i32: 0, 9, 10, 11, 4, 13, 14, 15>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %301 = "llvm.add"(%294, %111) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %302 = "llvm.add"(%297, %112) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %303 = "llvm.add"(%300, %112) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %304 = "llvm.ashr"(%301, %113) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %305 = "llvm.ashr"(%302, %113) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %306 = "llvm.ashr"(%303, %114) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %307 = "llvm.mul"(%306, %132) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %308 = "llvm.and"(%301, %133) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %309 = "llvm.shufflevector"(%307, %306) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %310 = "llvm.add"(%308, %134) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %311 = "llvm.add"(%310, %309) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %312 = "llvm.and"(%302, %133) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %313 = "llvm.add"(%304, %135) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %314 = "llvm.add"(%313, %312) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %315 = "llvm.and"(%303, %136) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %316 = "llvm.add"(%305, %135) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %317 = "llvm.add"(%316, %315) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %318 = "llvm.shufflevector"(%311, %1) <{mask = array<i32: 0, 1, 1, 0, 4, 5, 5, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %319 = "llvm.shufflevector"(%314, %1) <{mask = array<i32: 0, 1, 1, 0, 4, 5, 5, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %320 = "llvm.shufflevector"(%317, %1) <{mask = array<i32: 0, 1, 1, 0, 4, 5, 5, 4>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %321 = "llvm.shufflevector"(%311, %1) <{mask = array<i32: 2, 3, 2, 3, 6, 7, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %322 = "llvm.shufflevector"(%314, %1) <{mask = array<i32: 2, 3, 2, 3, 6, 7, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %323 = "llvm.shufflevector"(%317, %1) <{mask = array<i32: 2, 3, 2, 3, 6, 7, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.intr.lifetime.start"(%147) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%148) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%149) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.call"(%147, %148, %149, %318, %319, %320, %321, %322, %323) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_quad_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>) -> ()
    %324 = "llvm.load"(%147) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %325 = "llvm.load"(%148) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %326 = "llvm.load"(%149) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    "llvm.intr.lifetime.end"(%149) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%148) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%147) <{size = 64 : i64}> : (!llvm.ptr) -> ()
    %327 = "llvm.lshr"(%324, %113) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %328 = "llvm.lshr"(%325, %113) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %329 = "llvm.lshr"(%326, %114) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %330 = "llvm.mul"(%329, %132) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %331 = "llvm.and"(%324, %133) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %332 = "llvm.shufflevector"(%330, %329) <{mask = array<i32: 4, 5, 6, 7, 8, 9, 10, 11>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %333 = "llvm.add"(%332, %331) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %334 = "llvm.and"(%325, %133) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %335 = "llvm.add"(%334, %327) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %336 = "llvm.and"(%326, %136) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %337 = "llvm.add"(%336, %328) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %338 = "llvm.add"(%249, %137) <{overflowFlags = #llvm.overflow<none>}> : (i8, i8) -> i8
    %339 = "llvm.zext"(%338) : (i8) -> i32
    %340 = "llvm.icmp"(%339, %arg2) <{predicate = 6 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%340, %337, %335, %333, %338)[^bb3, ^bb1] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 4, 0>}> : (i1, vector<8xi64>, vector<8xi64>, vector<8xi64>, i8) -> ()
}
]

def fd_ed25519_point_dbln :
    Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 32, SLLVM.Ty.ptr, SLLVM.Ty.ptr])
      [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| fd_ed25519_point_dbln_region with
    @fd_r43x6_quad_sqr_fast := fd_r43x6_quad_sqr_fast,
    @fd_r43x6_quad_mul_fast := fd_r43x6_quad_mul_fast]

end Firedancer.Avx512

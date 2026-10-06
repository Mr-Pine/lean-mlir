module

public import SSA.Projects.RIR.Syntax.Elab

/-! Compiler-generated pure observations of the pinned AVX2 square kernel.
Each region is copied verbatim from its generated MLIR artifact. The LLVM
inlining pass and its pre-pass input are recorded by the extraction manifest.
-/
namespace Agave.Ed25519.Avx2SquareNegateD
@[expose] public section

mlir_def observe0 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.poison"() : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %2 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %3 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %4 = "llvm.insertelement"(%2, %1, %3) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %5 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %6 = "llvm.insertelement"(%4, %1, %5) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %7 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %8 = "llvm.insertelement"(%6, %0, %7) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %9 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %10 = "llvm.insertelement"(%8, %0, %9) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %11 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %12 = "llvm.insertelement"(%10, %1, %11) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %13 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %14 = "llvm.insertelement"(%12, %1, %13) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %15 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %16 = "llvm.insertelement"(%14, %0, %15) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %17 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %18 = "llvm.insertelement"(%16, %0, %17) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %19 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %20 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %21 = "llvm.insertelement"(%19, %0, %20) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %22 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %23 = "llvm.insertelement"(%21, %0, %22) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %24 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %25 = "llvm.insertelement"(%23, %1, %24) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %26 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %27 = "llvm.insertelement"(%25, %1, %26) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %28 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %29 = "llvm.insertelement"(%27, %0, %28) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %30 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %31 = "llvm.insertelement"(%29, %0, %30) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %32 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %33 = "llvm.insertelement"(%31, %1, %32) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %34 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %35 = "llvm.insertelement"(%33, %1, %34) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %36 = "llvm.mlir.constant"() <{value = dense<1> : vector<8xi32>}> : () -> vector<8xi32>
    %37 = "llvm.mlir.constant"() <{value = dense<19> : vector<4xi64>}> : () -> vector<4xi64>
    %38 = "llvm.mlir.constant"() <{value = dense<4294967295> : vector<4xi64>}> : () -> vector<4xi64>
    %39 = "llvm.mlir.constant"() <{value = dense<1> : vector<4xi64>}> : () -> vector<4xi64>
    %40 = "llvm.mlir.constant"() <{value = 9223369425514659840 : i64}> : () -> i64
    %41 = "llvm.mlir.poison"() : () -> i64
    %42 = "llvm.mlir.undef"() : () -> vector<4xi64>
    %43 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %44 = "llvm.insertelement"(%42, %41, %43) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %45 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %46 = "llvm.insertelement"(%44, %41, %45) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %47 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %48 = "llvm.insertelement"(%46, %41, %47) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %49 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %50 = "llvm.insertelement"(%48, %40, %49) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %51 = "llvm.mlir.constant"() <{value = 4611685880988434432 : i64}> : () -> i64
    %52 = "llvm.mlir.undef"() : () -> vector<4xi64>
    %53 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %54 = "llvm.insertelement"(%52, %41, %53) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %55 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %56 = "llvm.insertelement"(%54, %41, %55) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %57 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %58 = "llvm.insertelement"(%56, %41, %57) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %59 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %60 = "llvm.insertelement"(%58, %51, %59) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %61 = "llvm.mlir.constant"() <{value = 9223371899415822336 : i64}> : () -> i64
    %62 = "llvm.mlir.undef"() : () -> vector<4xi64>
    %63 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %64 = "llvm.insertelement"(%62, %41, %63) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %65 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %66 = "llvm.insertelement"(%64, %41, %65) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %67 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %68 = "llvm.insertelement"(%66, %41, %67) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %69 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %70 = "llvm.insertelement"(%68, %61, %69) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %71 = "llvm.mlir.constant"() <{value = dense<26> : vector<4xi64>}> : () -> vector<4xi64>
    %72 = "llvm.mlir.constant"() <{value = dense<67108863> : vector<4xi64>}> : () -> vector<4xi64>
    %73 = "llvm.mlir.constant"() <{value = dense<33554431> : vector<4xi64>}> : () -> vector<4xi64>
    %74 = "llvm.mlir.constant"() <{value = dense<25> : vector<4xi64>}> : () -> vector<4xi64>
    %75 = "llvm.mlir.constant"() <{value = dense<51> : vector<4xi64>}> : () -> vector<4xi64>
    %76 = "llvm.mlir.constant"() <{value = 67108863 : i32}> : () -> i32
    %77 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %78 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %79 = "llvm.insertelement"(%77, %76, %78) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %80 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %81 = "llvm.insertelement"(%79, %0, %80) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %82 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %83 = "llvm.insertelement"(%81, %76, %82) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %84 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %85 = "llvm.insertelement"(%83, %0, %84) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %86 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %87 = "llvm.insertelement"(%85, %76, %86) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %88 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %89 = "llvm.insertelement"(%87, %0, %88) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %90 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %91 = "llvm.insertelement"(%89, %76, %90) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %92 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %93 = "llvm.insertelement"(%91, %0, %92) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %94 = "llvm.bitcast"(%arg0) : (vector<4xi64>) -> vector<8xi32>
    %95 = "llvm.shufflevector"(%94, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %96 = "llvm.shufflevector"(%94, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %97 = "llvm.bitcast"(%95) : (vector<8xi32>) -> vector<4xi64>
    %98 = "llvm.bitcast"(%96) : (vector<8xi32>) -> vector<4xi64>
    %99 = "llvm.bitcast"(%arg1) : (vector<4xi64>) -> vector<8xi32>
    %100 = "llvm.shufflevector"(%99, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %101 = "llvm.shufflevector"(%99, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %102 = "llvm.bitcast"(%100) : (vector<8xi32>) -> vector<4xi64>
    %103 = "llvm.bitcast"(%101) : (vector<8xi32>) -> vector<4xi64>
    %104 = "llvm.bitcast"(%arg2) : (vector<4xi64>) -> vector<8xi32>
    %105 = "llvm.shufflevector"(%104, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %106 = "llvm.shufflevector"(%104, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %107 = "llvm.bitcast"(%105) : (vector<8xi32>) -> vector<4xi64>
    %108 = "llvm.bitcast"(%106) : (vector<8xi32>) -> vector<4xi64>
    %109 = "llvm.bitcast"(%arg3) : (vector<4xi64>) -> vector<8xi32>
    %110 = "llvm.shufflevector"(%109, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %111 = "llvm.shufflevector"(%109, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %112 = "llvm.bitcast"(%110) : (vector<8xi32>) -> vector<4xi64>
    %113 = "llvm.bitcast"(%111) : (vector<8xi32>) -> vector<4xi64>
    %114 = "llvm.bitcast"(%arg4) : (vector<4xi64>) -> vector<8xi32>
    %115 = "llvm.shufflevector"(%114, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %116 = "llvm.shufflevector"(%114, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %117 = "llvm.bitcast"(%115) : (vector<8xi32>) -> vector<4xi64>
    %118 = "llvm.bitcast"(%116) : (vector<8xi32>) -> vector<4xi64>
    %119 = "llvm.shl"(%95, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %120 = "llvm.bitcast"(%119) : (vector<8xi32>) -> vector<4xi64>
    %121 = "llvm.shl"(%96, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %122 = "llvm.bitcast"(%121) : (vector<8xi32>) -> vector<4xi64>
    %123 = "llvm.shl"(%100, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %124 = "llvm.bitcast"(%123) : (vector<8xi32>) -> vector<4xi64>
    %125 = "llvm.shl"(%101, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %126 = "llvm.bitcast"(%125) : (vector<8xi32>) -> vector<4xi64>
    %127 = "llvm.shl"(%105, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %128 = "llvm.bitcast"(%127) : (vector<8xi32>) -> vector<4xi64>
    %129 = "llvm.shl"(%106, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %130 = "llvm.bitcast"(%129) : (vector<8xi32>) -> vector<4xi64>
    %131 = "llvm.shl"(%110, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %132 = "llvm.bitcast"(%131) : (vector<8xi32>) -> vector<4xi64>
    %133 = "llvm.shl"(%111, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %134 = "llvm.bitcast"(%133) : (vector<8xi32>) -> vector<4xi64>
    %135 = "llvm.mul"(%108, %37) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %136 = "llvm.mul"(%112, %37) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %137 = "llvm.mul"(%113, %37) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %138 = "llvm.mul"(%117, %37) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %139 = "llvm.mul"(%118, %37) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %140 = "llvm.mul"(%97, %97) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %141 = "llvm.and"(%138, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %142 = "llvm.mul"(%141, %124) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %143 = "llvm.and"(%136, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %144 = "llvm.mul"(%143, %128) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %145 = "llvm.and"(%139, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %146 = "llvm.mul"(%145, %122) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %147 = "llvm.and"(%137, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %148 = "llvm.mul"(%147, %126) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %149 = "llvm.and"(%135, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %150 = "llvm.mul"(%149, %108) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %151 = "llvm.add"(%148, %150) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %152 = "llvm.add"(%151, %146) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %153 = "llvm.shl"(%152, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %154 = "llvm.add"(%144, %140) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %155 = "llvm.add"(%154, %142) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %156 = "llvm.add"(%155, %153) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %157 = "llvm.mul"(%120, %98) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %158 = "llvm.mul"(%141, %126) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %159 = "llvm.mul"(%143, %130) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %160 = "llvm.mul"(%145, %102) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %161 = "llvm.mul"(%147, %107) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %162 = "llvm.add"(%160, %161) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %163 = "llvm.shl"(%162, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %164 = "llvm.add"(%159, %157) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %165 = "llvm.add"(%164, %158) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %166 = "llvm.add"(%165, %163) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %167 = "llvm.mul"(%107, %120) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %168 = "llvm.mul"(%126, %122) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %169 = "llvm.mul"(%102, %102) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %170 = "llvm.mul"(%141, %132) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %171 = "llvm.mul"(%145, %130) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %172 = "llvm.mul"(%147, %113) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %173 = "llvm.add"(%171, %172) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %174 = "llvm.shl"(%173, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %175 = "llvm.add"(%167, %169) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %176 = "llvm.add"(%175, %168) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %177 = "llvm.add"(%176, %170) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %178 = "llvm.add"(%177, %174) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %179 = "llvm.mul"(%108, %120) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %180 = "llvm.mul"(%107, %122) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %181 = "llvm.add"(%180, %179) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %182 = "llvm.mul"(%124, %103) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %183 = "llvm.add"(%181, %182) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %184 = "llvm.mul"(%141, %134) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %185 = "llvm.add"(%183, %184) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %186 = "llvm.mul"(%145, %112) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %187 = "llvm.shl"(%186, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %188 = "llvm.add"(%185, %187) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %189 = "llvm.mul"(%112, %120) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %190 = "llvm.mul"(%130, %122) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %191 = "llvm.mul"(%107, %124) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %192 = "llvm.mul"(%126, %103) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %193 = "llvm.mul"(%141, %117) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %194 = "llvm.mul"(%145, %134) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %195 = "llvm.shl"(%194, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %196 = "llvm.add"(%192, %191) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %197 = "llvm.add"(%196, %189) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %198 = "llvm.add"(%197, %190) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %199 = "llvm.add"(%198, %193) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %200 = "llvm.add"(%199, %195) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %201 = "llvm.mul"(%113, %120) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %202 = "llvm.mul"(%112, %122) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %203 = "llvm.mul"(%108, %124) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %204 = "llvm.mul"(%107, %126) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %205 = "llvm.mul"(%145, %117) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %206 = "llvm.shl"(%205, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %207 = "llvm.add"(%204, %203) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %208 = "llvm.add"(%207, %201) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %209 = "llvm.add"(%208, %202) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %210 = "llvm.add"(%209, %206) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %211 = "llvm.mul"(%117, %120) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %212 = "llvm.mul"(%134, %122) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %213 = "llvm.mul"(%112, %124) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %214 = "llvm.mul"(%130, %126) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %215 = "llvm.mul"(%107, %107) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %216 = "llvm.mul"(%145, %118) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %217 = "llvm.shl"(%216, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %218 = "llvm.add"(%213, %215) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %219 = "llvm.add"(%218, %214) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %220 = "llvm.add"(%219, %211) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %221 = "llvm.add"(%220, %212) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %222 = "llvm.add"(%221, %217) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %223 = "llvm.mul"(%118, %120) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %224 = "llvm.mul"(%117, %122) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %225 = "llvm.mul"(%113, %124) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %226 = "llvm.mul"(%112, %126) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %227 = "llvm.mul"(%128, %108) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %228 = "llvm.add"(%226, %225) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %229 = "llvm.add"(%228, %227) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %230 = "llvm.add"(%229, %223) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %231 = "llvm.add"(%230, %224) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %232 = "llvm.sub"(%50, %156) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %233 = "llvm.shufflevector"(%156, %232) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %234 = "llvm.sub"(%60, %166) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %235 = "llvm.shufflevector"(%166, %234) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %236 = "llvm.sub"(%70, %178) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %237 = "llvm.shufflevector"(%178, %236) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %238 = "llvm.sub"(%60, %188) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %239 = "llvm.shufflevector"(%188, %238) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %240 = "llvm.sub"(%70, %200) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %241 = "llvm.shufflevector"(%200, %240) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %242 = "llvm.sub"(%60, %210) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %243 = "llvm.shufflevector"(%210, %242) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %244 = "llvm.sub"(%70, %222) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %245 = "llvm.shufflevector"(%222, %244) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %246 = "llvm.sub"(%60, %231) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %247 = "llvm.shufflevector"(%231, %246) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %248 = "llvm.lshr"(%233, %71) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %249 = "llvm.add"(%248, %235) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %250 = "llvm.and"(%233, %72) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %251 = "llvm.lshr"(%237, %71) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %252 = "llvm.add"(%251, %239) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %253 = "llvm.and"(%249, %73) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %254 = "llvm.lshr"(%252, %74) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %255 = "llvm.add"(%254, %241) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %256 = "llvm.lshr"(%255, %71) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %257 = "llvm.add"(%256, %243) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %258 = "llvm.lshr"(%257, %74) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %259 = "llvm.add"(%258, %245) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %260 = "llvm.lshr"(%259, %71) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %261 = "llvm.add"(%260, %247) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %262 = "llvm.lshr"(%261, %74) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %263 = "llvm.and"(%262, %72) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %264 = "llvm.lshr"(%261, %75) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %265 = "llvm.mul"(%263, %37) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %266 = "llvm.mul"(%264, %37) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %267 = "llvm.add"(%265, %250) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %268 = "llvm.add"(%266, %253) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %269 = "llvm.lshr"(%267, %71) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %270 = "llvm.add"(%268, %269) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %271 = "llvm.bitcast"(%267) : (vector<4xi64>) -> vector<8xi32>
    %272 = "llvm.and"(%271, %93) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %273 = "llvm.bitcast"(%270) : (vector<4xi64>) -> vector<8xi32>
    %274 = "llvm.shufflevector"(%272, %273) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %275 = "llvm.bitcast"(%274) : (vector<8xi32>) -> vector<4xi64>
    "llvm.return"(%275) : (vector<4xi64>) -> ()
}

mlir_def observe1 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.poison"() : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %2 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %3 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %4 = "llvm.insertelement"(%2, %1, %3) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %5 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %6 = "llvm.insertelement"(%4, %1, %5) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %7 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %8 = "llvm.insertelement"(%6, %0, %7) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %9 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %10 = "llvm.insertelement"(%8, %0, %9) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %11 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %12 = "llvm.insertelement"(%10, %1, %11) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %13 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %14 = "llvm.insertelement"(%12, %1, %13) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %15 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %16 = "llvm.insertelement"(%14, %0, %15) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %17 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %18 = "llvm.insertelement"(%16, %0, %17) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %19 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %20 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %21 = "llvm.insertelement"(%19, %0, %20) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %22 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %23 = "llvm.insertelement"(%21, %0, %22) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %24 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %25 = "llvm.insertelement"(%23, %1, %24) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %26 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %27 = "llvm.insertelement"(%25, %1, %26) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %28 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %29 = "llvm.insertelement"(%27, %0, %28) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %30 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %31 = "llvm.insertelement"(%29, %0, %30) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %32 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %33 = "llvm.insertelement"(%31, %1, %32) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %34 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %35 = "llvm.insertelement"(%33, %1, %34) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %36 = "llvm.mlir.constant"() <{value = dense<1> : vector<8xi32>}> : () -> vector<8xi32>
    %37 = "llvm.mlir.constant"() <{value = dense<19> : vector<4xi64>}> : () -> vector<4xi64>
    %38 = "llvm.mlir.constant"() <{value = dense<4294967295> : vector<4xi64>}> : () -> vector<4xi64>
    %39 = "llvm.mlir.constant"() <{value = dense<1> : vector<4xi64>}> : () -> vector<4xi64>
    %40 = "llvm.mlir.constant"() <{value = 9223369425514659840 : i64}> : () -> i64
    %41 = "llvm.mlir.poison"() : () -> i64
    %42 = "llvm.mlir.undef"() : () -> vector<4xi64>
    %43 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %44 = "llvm.insertelement"(%42, %41, %43) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %45 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %46 = "llvm.insertelement"(%44, %41, %45) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %47 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %48 = "llvm.insertelement"(%46, %41, %47) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %49 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %50 = "llvm.insertelement"(%48, %40, %49) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %51 = "llvm.mlir.constant"() <{value = 4611685880988434432 : i64}> : () -> i64
    %52 = "llvm.mlir.undef"() : () -> vector<4xi64>
    %53 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %54 = "llvm.insertelement"(%52, %41, %53) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %55 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %56 = "llvm.insertelement"(%54, %41, %55) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %57 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %58 = "llvm.insertelement"(%56, %41, %57) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %59 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %60 = "llvm.insertelement"(%58, %51, %59) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %61 = "llvm.mlir.constant"() <{value = 9223371899415822336 : i64}> : () -> i64
    %62 = "llvm.mlir.undef"() : () -> vector<4xi64>
    %63 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %64 = "llvm.insertelement"(%62, %41, %63) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %65 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %66 = "llvm.insertelement"(%64, %41, %65) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %67 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %68 = "llvm.insertelement"(%66, %41, %67) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %69 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %70 = "llvm.insertelement"(%68, %61, %69) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %71 = "llvm.mlir.constant"() <{value = dense<26> : vector<4xi64>}> : () -> vector<4xi64>
    %72 = "llvm.mlir.constant"() <{value = dense<25> : vector<4xi64>}> : () -> vector<4xi64>
    %73 = "llvm.mlir.constant"() <{value = 67108863 : i32}> : () -> i32
    %74 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %75 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %76 = "llvm.insertelement"(%74, %73, %75) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %77 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %78 = "llvm.insertelement"(%76, %0, %77) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %79 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %80 = "llvm.insertelement"(%78, %73, %79) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %81 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %82 = "llvm.insertelement"(%80, %0, %81) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %83 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %84 = "llvm.insertelement"(%82, %73, %83) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %85 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %86 = "llvm.insertelement"(%84, %0, %85) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %87 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %88 = "llvm.insertelement"(%86, %73, %87) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %89 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %90 = "llvm.insertelement"(%88, %0, %89) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %91 = "llvm.mlir.constant"() <{value = 33554431 : i32}> : () -> i32
    %92 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %93 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %94 = "llvm.insertelement"(%92, %91, %93) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %95 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %96 = "llvm.insertelement"(%94, %0, %95) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %97 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %98 = "llvm.insertelement"(%96, %91, %97) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %99 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %100 = "llvm.insertelement"(%98, %0, %99) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %101 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %102 = "llvm.insertelement"(%100, %91, %101) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %103 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %104 = "llvm.insertelement"(%102, %0, %103) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %105 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %106 = "llvm.insertelement"(%104, %91, %105) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %107 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %108 = "llvm.insertelement"(%106, %0, %107) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %109 = "llvm.bitcast"(%arg0) : (vector<4xi64>) -> vector<8xi32>
    %110 = "llvm.shufflevector"(%109, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %111 = "llvm.shufflevector"(%109, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %112 = "llvm.bitcast"(%110) : (vector<8xi32>) -> vector<4xi64>
    %113 = "llvm.bitcast"(%111) : (vector<8xi32>) -> vector<4xi64>
    %114 = "llvm.bitcast"(%arg1) : (vector<4xi64>) -> vector<8xi32>
    %115 = "llvm.shufflevector"(%114, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %116 = "llvm.shufflevector"(%114, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %117 = "llvm.bitcast"(%115) : (vector<8xi32>) -> vector<4xi64>
    %118 = "llvm.bitcast"(%116) : (vector<8xi32>) -> vector<4xi64>
    %119 = "llvm.bitcast"(%arg2) : (vector<4xi64>) -> vector<8xi32>
    %120 = "llvm.shufflevector"(%119, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %121 = "llvm.shufflevector"(%119, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %122 = "llvm.bitcast"(%120) : (vector<8xi32>) -> vector<4xi64>
    %123 = "llvm.bitcast"(%121) : (vector<8xi32>) -> vector<4xi64>
    %124 = "llvm.bitcast"(%arg3) : (vector<4xi64>) -> vector<8xi32>
    %125 = "llvm.shufflevector"(%124, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %126 = "llvm.shufflevector"(%124, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %127 = "llvm.bitcast"(%125) : (vector<8xi32>) -> vector<4xi64>
    %128 = "llvm.bitcast"(%126) : (vector<8xi32>) -> vector<4xi64>
    %129 = "llvm.bitcast"(%arg4) : (vector<4xi64>) -> vector<8xi32>
    %130 = "llvm.shufflevector"(%129, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %131 = "llvm.shufflevector"(%129, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %132 = "llvm.bitcast"(%130) : (vector<8xi32>) -> vector<4xi64>
    %133 = "llvm.bitcast"(%131) : (vector<8xi32>) -> vector<4xi64>
    %134 = "llvm.shl"(%110, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %135 = "llvm.bitcast"(%134) : (vector<8xi32>) -> vector<4xi64>
    %136 = "llvm.shl"(%111, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %137 = "llvm.bitcast"(%136) : (vector<8xi32>) -> vector<4xi64>
    %138 = "llvm.shl"(%115, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %139 = "llvm.bitcast"(%138) : (vector<8xi32>) -> vector<4xi64>
    %140 = "llvm.shl"(%116, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %141 = "llvm.bitcast"(%140) : (vector<8xi32>) -> vector<4xi64>
    %142 = "llvm.shl"(%120, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %143 = "llvm.bitcast"(%142) : (vector<8xi32>) -> vector<4xi64>
    %144 = "llvm.shl"(%121, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %145 = "llvm.bitcast"(%144) : (vector<8xi32>) -> vector<4xi64>
    %146 = "llvm.mul"(%123, %37) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %147 = "llvm.mul"(%127, %37) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %148 = "llvm.mul"(%128, %37) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %149 = "llvm.mul"(%132, %37) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %150 = "llvm.mul"(%133, %37) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %151 = "llvm.mul"(%112, %112) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %152 = "llvm.and"(%149, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %153 = "llvm.mul"(%152, %139) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %154 = "llvm.and"(%147, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %155 = "llvm.mul"(%154, %143) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %156 = "llvm.and"(%150, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %157 = "llvm.mul"(%156, %137) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %158 = "llvm.and"(%148, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %159 = "llvm.mul"(%158, %141) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %160 = "llvm.and"(%146, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %161 = "llvm.mul"(%160, %123) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %162 = "llvm.add"(%159, %161) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %163 = "llvm.add"(%162, %157) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %164 = "llvm.shl"(%163, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %165 = "llvm.add"(%155, %151) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %166 = "llvm.add"(%165, %153) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %167 = "llvm.add"(%166, %164) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %168 = "llvm.mul"(%135, %113) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %169 = "llvm.mul"(%152, %141) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %170 = "llvm.mul"(%154, %145) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %171 = "llvm.mul"(%156, %117) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %172 = "llvm.mul"(%158, %122) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %173 = "llvm.add"(%171, %172) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %174 = "llvm.shl"(%173, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %175 = "llvm.add"(%170, %168) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %176 = "llvm.add"(%175, %169) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %177 = "llvm.add"(%176, %174) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %178 = "llvm.mul"(%117, %135) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %179 = "llvm.mul"(%137, %113) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %180 = "llvm.add"(%179, %178) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %181 = "llvm.mul"(%152, %143) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %182 = "llvm.mul"(%154, %127) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %183 = "llvm.mul"(%156, %141) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %184 = "llvm.mul"(%158, %145) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %185 = "llvm.add"(%183, %184) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %186 = "llvm.shl"(%185, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %187 = "llvm.add"(%180, %182) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %188 = "llvm.add"(%187, %181) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %189 = "llvm.add"(%188, %186) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %190 = "llvm.mul"(%118, %135) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %191 = "llvm.mul"(%117, %137) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %192 = "llvm.add"(%191, %190) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %193 = "llvm.mul"(%152, %145) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %194 = "llvm.add"(%192, %193) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %195 = "llvm.mul"(%156, %122) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %196 = "llvm.mul"(%158, %127) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %197 = "llvm.add"(%195, %196) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %198 = "llvm.shl"(%197, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %199 = "llvm.add"(%194, %198) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %200 = "llvm.sub"(%50, %167) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %201 = "llvm.shufflevector"(%167, %200) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %202 = "llvm.sub"(%60, %177) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %203 = "llvm.shufflevector"(%177, %202) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %204 = "llvm.sub"(%70, %189) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %205 = "llvm.shufflevector"(%189, %204) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %206 = "llvm.sub"(%60, %199) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %207 = "llvm.shufflevector"(%199, %206) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %208 = "llvm.lshr"(%201, %71) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %209 = "llvm.add"(%208, %203) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %210 = "llvm.lshr"(%209, %72) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %211 = "llvm.add"(%210, %205) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %212 = "llvm.lshr"(%211, %71) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %213 = "llvm.add"(%212, %207) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %214 = "llvm.bitcast"(%211) : (vector<4xi64>) -> vector<8xi32>
    %215 = "llvm.and"(%214, %90) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %216 = "llvm.bitcast"(%213) : (vector<4xi64>) -> vector<8xi32>
    %217 = "llvm.and"(%216, %108) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %218 = "llvm.shufflevector"(%215, %217) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %219 = "llvm.bitcast"(%218) : (vector<8xi32>) -> vector<4xi64>
    "llvm.return"(%219) : (vector<4xi64>) -> ()
}

mlir_def observe2 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.poison"() : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %2 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %3 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %4 = "llvm.insertelement"(%2, %1, %3) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %5 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %6 = "llvm.insertelement"(%4, %1, %5) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %7 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %8 = "llvm.insertelement"(%6, %0, %7) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %9 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %10 = "llvm.insertelement"(%8, %0, %9) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %11 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %12 = "llvm.insertelement"(%10, %1, %11) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %13 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %14 = "llvm.insertelement"(%12, %1, %13) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %15 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %16 = "llvm.insertelement"(%14, %0, %15) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %17 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %18 = "llvm.insertelement"(%16, %0, %17) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %19 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %20 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %21 = "llvm.insertelement"(%19, %0, %20) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %22 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %23 = "llvm.insertelement"(%21, %0, %22) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %24 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %25 = "llvm.insertelement"(%23, %1, %24) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %26 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %27 = "llvm.insertelement"(%25, %1, %26) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %28 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %29 = "llvm.insertelement"(%27, %0, %28) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %30 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %31 = "llvm.insertelement"(%29, %0, %30) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %32 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %33 = "llvm.insertelement"(%31, %1, %32) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %34 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %35 = "llvm.insertelement"(%33, %1, %34) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %36 = "llvm.mlir.constant"() <{value = dense<1> : vector<8xi32>}> : () -> vector<8xi32>
    %37 = "llvm.mlir.constant"() <{value = dense<19> : vector<4xi64>}> : () -> vector<4xi64>
    %38 = "llvm.mlir.constant"() <{value = dense<4294967295> : vector<4xi64>}> : () -> vector<4xi64>
    %39 = "llvm.mlir.constant"() <{value = dense<1> : vector<4xi64>}> : () -> vector<4xi64>
    %40 = "llvm.mlir.constant"() <{value = 9223369425514659840 : i64}> : () -> i64
    %41 = "llvm.mlir.poison"() : () -> i64
    %42 = "llvm.mlir.undef"() : () -> vector<4xi64>
    %43 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %44 = "llvm.insertelement"(%42, %41, %43) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %45 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %46 = "llvm.insertelement"(%44, %41, %45) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %47 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %48 = "llvm.insertelement"(%46, %41, %47) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %49 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %50 = "llvm.insertelement"(%48, %40, %49) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %51 = "llvm.mlir.constant"() <{value = 4611685880988434432 : i64}> : () -> i64
    %52 = "llvm.mlir.undef"() : () -> vector<4xi64>
    %53 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %54 = "llvm.insertelement"(%52, %41, %53) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %55 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %56 = "llvm.insertelement"(%54, %41, %55) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %57 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %58 = "llvm.insertelement"(%56, %41, %57) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %59 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %60 = "llvm.insertelement"(%58, %51, %59) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %61 = "llvm.mlir.constant"() <{value = 9223371899415822336 : i64}> : () -> i64
    %62 = "llvm.mlir.undef"() : () -> vector<4xi64>
    %63 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %64 = "llvm.insertelement"(%62, %41, %63) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %65 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %66 = "llvm.insertelement"(%64, %41, %65) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %67 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %68 = "llvm.insertelement"(%66, %41, %67) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %69 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %70 = "llvm.insertelement"(%68, %61, %69) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %71 = "llvm.mlir.constant"() <{value = dense<26> : vector<4xi64>}> : () -> vector<4xi64>
    %72 = "llvm.mlir.constant"() <{value = dense<67108863> : vector<4xi64>}> : () -> vector<4xi64>
    %73 = "llvm.mlir.constant"() <{value = dense<25> : vector<4xi64>}> : () -> vector<4xi64>
    %74 = "llvm.mlir.constant"() <{value = dense<33554431> : vector<4xi64>}> : () -> vector<4xi64>
    %75 = "llvm.mlir.constant"() <{value = 67108863 : i32}> : () -> i32
    %76 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %77 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %78 = "llvm.insertelement"(%76, %75, %77) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %79 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %80 = "llvm.insertelement"(%78, %0, %79) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %81 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %82 = "llvm.insertelement"(%80, %75, %81) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %83 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %84 = "llvm.insertelement"(%82, %0, %83) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %85 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %86 = "llvm.insertelement"(%84, %75, %85) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %87 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %88 = "llvm.insertelement"(%86, %0, %87) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %89 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %90 = "llvm.insertelement"(%88, %75, %89) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %91 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %92 = "llvm.insertelement"(%90, %0, %91) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %93 = "llvm.bitcast"(%arg0) : (vector<4xi64>) -> vector<8xi32>
    %94 = "llvm.shufflevector"(%93, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %95 = "llvm.shufflevector"(%93, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %96 = "llvm.bitcast"(%94) : (vector<8xi32>) -> vector<4xi64>
    %97 = "llvm.bitcast"(%95) : (vector<8xi32>) -> vector<4xi64>
    %98 = "llvm.bitcast"(%arg1) : (vector<4xi64>) -> vector<8xi32>
    %99 = "llvm.shufflevector"(%98, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %100 = "llvm.shufflevector"(%98, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %101 = "llvm.bitcast"(%99) : (vector<8xi32>) -> vector<4xi64>
    %102 = "llvm.bitcast"(%100) : (vector<8xi32>) -> vector<4xi64>
    %103 = "llvm.bitcast"(%arg2) : (vector<4xi64>) -> vector<8xi32>
    %104 = "llvm.shufflevector"(%103, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %105 = "llvm.shufflevector"(%103, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %106 = "llvm.bitcast"(%104) : (vector<8xi32>) -> vector<4xi64>
    %107 = "llvm.bitcast"(%105) : (vector<8xi32>) -> vector<4xi64>
    %108 = "llvm.bitcast"(%arg3) : (vector<4xi64>) -> vector<8xi32>
    %109 = "llvm.shufflevector"(%108, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %110 = "llvm.shufflevector"(%108, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %111 = "llvm.bitcast"(%109) : (vector<8xi32>) -> vector<4xi64>
    %112 = "llvm.bitcast"(%110) : (vector<8xi32>) -> vector<4xi64>
    %113 = "llvm.bitcast"(%arg4) : (vector<4xi64>) -> vector<8xi32>
    %114 = "llvm.shufflevector"(%113, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %115 = "llvm.shufflevector"(%113, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %116 = "llvm.bitcast"(%114) : (vector<8xi32>) -> vector<4xi64>
    %117 = "llvm.bitcast"(%115) : (vector<8xi32>) -> vector<4xi64>
    %118 = "llvm.shl"(%94, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %119 = "llvm.bitcast"(%118) : (vector<8xi32>) -> vector<4xi64>
    %120 = "llvm.shl"(%95, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %121 = "llvm.bitcast"(%120) : (vector<8xi32>) -> vector<4xi64>
    %122 = "llvm.shl"(%99, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %123 = "llvm.bitcast"(%122) : (vector<8xi32>) -> vector<4xi64>
    %124 = "llvm.shl"(%100, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %125 = "llvm.bitcast"(%124) : (vector<8xi32>) -> vector<4xi64>
    %126 = "llvm.shl"(%104, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %127 = "llvm.bitcast"(%126) : (vector<8xi32>) -> vector<4xi64>
    %128 = "llvm.shl"(%105, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %129 = "llvm.bitcast"(%128) : (vector<8xi32>) -> vector<4xi64>
    %130 = "llvm.shl"(%109, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %131 = "llvm.bitcast"(%130) : (vector<8xi32>) -> vector<4xi64>
    %132 = "llvm.shl"(%110, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %133 = "llvm.bitcast"(%132) : (vector<8xi32>) -> vector<4xi64>
    %134 = "llvm.mul"(%107, %37) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %135 = "llvm.mul"(%111, %37) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %136 = "llvm.mul"(%112, %37) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %137 = "llvm.mul"(%116, %37) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %138 = "llvm.mul"(%117, %37) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %139 = "llvm.mul"(%96, %96) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %140 = "llvm.and"(%137, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %141 = "llvm.mul"(%140, %123) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %142 = "llvm.and"(%135, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %143 = "llvm.mul"(%142, %127) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %144 = "llvm.and"(%138, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %145 = "llvm.mul"(%144, %121) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %146 = "llvm.and"(%136, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %147 = "llvm.mul"(%146, %125) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %148 = "llvm.and"(%134, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %149 = "llvm.mul"(%148, %107) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %150 = "llvm.add"(%147, %149) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %151 = "llvm.add"(%150, %145) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %152 = "llvm.shl"(%151, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %153 = "llvm.add"(%143, %139) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %154 = "llvm.add"(%153, %141) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %155 = "llvm.add"(%154, %152) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %156 = "llvm.mul"(%119, %97) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %157 = "llvm.mul"(%140, %125) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %158 = "llvm.mul"(%142, %129) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %159 = "llvm.mul"(%144, %101) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %160 = "llvm.mul"(%146, %106) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %161 = "llvm.add"(%159, %160) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %162 = "llvm.shl"(%161, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %163 = "llvm.add"(%158, %156) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %164 = "llvm.add"(%163, %157) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %165 = "llvm.add"(%164, %162) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %166 = "llvm.mul"(%101, %119) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %167 = "llvm.mul"(%121, %97) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %168 = "llvm.add"(%167, %166) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %169 = "llvm.mul"(%140, %127) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %170 = "llvm.mul"(%142, %111) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %171 = "llvm.mul"(%144, %125) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %172 = "llvm.mul"(%146, %129) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %173 = "llvm.add"(%171, %172) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %174 = "llvm.shl"(%173, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %175 = "llvm.add"(%168, %170) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %176 = "llvm.add"(%175, %169) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %177 = "llvm.add"(%176, %174) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %178 = "llvm.mul"(%102, %119) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %179 = "llvm.mul"(%101, %121) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %180 = "llvm.add"(%179, %178) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %181 = "llvm.mul"(%140, %129) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %182 = "llvm.add"(%180, %181) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %183 = "llvm.mul"(%144, %106) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %184 = "llvm.mul"(%146, %111) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %185 = "llvm.add"(%183, %184) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %186 = "llvm.shl"(%185, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %187 = "llvm.add"(%182, %186) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %188 = "llvm.mul"(%106, %119) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %189 = "llvm.mul"(%125, %121) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %190 = "llvm.mul"(%101, %101) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %191 = "llvm.mul"(%140, %131) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %192 = "llvm.mul"(%144, %129) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %193 = "llvm.mul"(%146, %112) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %194 = "llvm.add"(%192, %193) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %195 = "llvm.shl"(%194, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %196 = "llvm.add"(%188, %190) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %197 = "llvm.add"(%196, %189) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %198 = "llvm.add"(%197, %191) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %199 = "llvm.add"(%198, %195) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %200 = "llvm.mul"(%107, %119) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %201 = "llvm.mul"(%106, %121) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %202 = "llvm.add"(%201, %200) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %203 = "llvm.mul"(%123, %102) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %204 = "llvm.add"(%202, %203) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %205 = "llvm.mul"(%140, %133) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %206 = "llvm.add"(%204, %205) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %207 = "llvm.mul"(%144, %111) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %208 = "llvm.shl"(%207, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %209 = "llvm.add"(%206, %208) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %210 = "llvm.sub"(%50, %155) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %211 = "llvm.shufflevector"(%155, %210) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %212 = "llvm.sub"(%60, %165) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %213 = "llvm.shufflevector"(%165, %212) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %214 = "llvm.sub"(%70, %177) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %215 = "llvm.shufflevector"(%177, %214) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %216 = "llvm.sub"(%60, %187) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %217 = "llvm.shufflevector"(%187, %216) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %218 = "llvm.sub"(%70, %199) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %219 = "llvm.shufflevector"(%199, %218) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %220 = "llvm.sub"(%60, %209) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %221 = "llvm.shufflevector"(%209, %220) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %222 = "llvm.lshr"(%211, %71) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %223 = "llvm.add"(%222, %213) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %224 = "llvm.lshr"(%219, %71) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %225 = "llvm.add"(%224, %221) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %226 = "llvm.and"(%219, %72) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %227 = "llvm.lshr"(%223, %73) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %228 = "llvm.add"(%227, %215) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %229 = "llvm.and"(%225, %74) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %230 = "llvm.lshr"(%228, %71) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %231 = "llvm.add"(%230, %217) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %232 = "llvm.lshr"(%231, %73) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %233 = "llvm.add"(%232, %226) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %234 = "llvm.lshr"(%233, %71) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %235 = "llvm.add"(%234, %229) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %236 = "llvm.bitcast"(%235) : (vector<4xi64>) -> vector<8xi32>
    %237 = "llvm.bitcast"(%233) : (vector<4xi64>) -> vector<8xi32>
    %238 = "llvm.and"(%237, %92) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %239 = "llvm.shufflevector"(%238, %236) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %240 = "llvm.bitcast"(%239) : (vector<8xi32>) -> vector<4xi64>
    "llvm.return"(%240) : (vector<4xi64>) -> ()
}

mlir_def observe3 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.poison"() : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %2 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %3 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %4 = "llvm.insertelement"(%2, %1, %3) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %5 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %6 = "llvm.insertelement"(%4, %1, %5) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %7 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %8 = "llvm.insertelement"(%6, %0, %7) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %9 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %10 = "llvm.insertelement"(%8, %0, %9) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %11 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %12 = "llvm.insertelement"(%10, %1, %11) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %13 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %14 = "llvm.insertelement"(%12, %1, %13) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %15 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %16 = "llvm.insertelement"(%14, %0, %15) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %17 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %18 = "llvm.insertelement"(%16, %0, %17) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %19 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %20 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %21 = "llvm.insertelement"(%19, %0, %20) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %22 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %23 = "llvm.insertelement"(%21, %0, %22) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %24 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %25 = "llvm.insertelement"(%23, %1, %24) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %26 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %27 = "llvm.insertelement"(%25, %1, %26) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %28 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %29 = "llvm.insertelement"(%27, %0, %28) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %30 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %31 = "llvm.insertelement"(%29, %0, %30) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %32 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %33 = "llvm.insertelement"(%31, %1, %32) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %34 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %35 = "llvm.insertelement"(%33, %1, %34) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %36 = "llvm.mlir.constant"() <{value = dense<1> : vector<8xi32>}> : () -> vector<8xi32>
    %37 = "llvm.mlir.constant"() <{value = dense<19> : vector<4xi64>}> : () -> vector<4xi64>
    %38 = "llvm.mlir.constant"() <{value = dense<4294967295> : vector<4xi64>}> : () -> vector<4xi64>
    %39 = "llvm.mlir.constant"() <{value = dense<1> : vector<4xi64>}> : () -> vector<4xi64>
    %40 = "llvm.mlir.constant"() <{value = 9223371899415822336 : i64}> : () -> i64
    %41 = "llvm.mlir.poison"() : () -> i64
    %42 = "llvm.mlir.undef"() : () -> vector<4xi64>
    %43 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %44 = "llvm.insertelement"(%42, %41, %43) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %45 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %46 = "llvm.insertelement"(%44, %41, %45) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %47 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %48 = "llvm.insertelement"(%46, %41, %47) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %49 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %50 = "llvm.insertelement"(%48, %40, %49) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %51 = "llvm.mlir.constant"() <{value = 4611685880988434432 : i64}> : () -> i64
    %52 = "llvm.mlir.undef"() : () -> vector<4xi64>
    %53 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %54 = "llvm.insertelement"(%52, %41, %53) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %55 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %56 = "llvm.insertelement"(%54, %41, %55) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %57 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %58 = "llvm.insertelement"(%56, %41, %57) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %59 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %60 = "llvm.insertelement"(%58, %51, %59) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %61 = "llvm.mlir.constant"() <{value = dense<26> : vector<4xi64>}> : () -> vector<4xi64>
    %62 = "llvm.mlir.constant"() <{value = dense<25> : vector<4xi64>}> : () -> vector<4xi64>
    %63 = "llvm.mlir.constant"() <{value = 67108863 : i32}> : () -> i32
    %64 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %65 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %66 = "llvm.insertelement"(%64, %63, %65) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %67 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %68 = "llvm.insertelement"(%66, %0, %67) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %69 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %70 = "llvm.insertelement"(%68, %63, %69) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %71 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %72 = "llvm.insertelement"(%70, %0, %71) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %73 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %74 = "llvm.insertelement"(%72, %63, %73) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %75 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %76 = "llvm.insertelement"(%74, %0, %75) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %77 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %78 = "llvm.insertelement"(%76, %63, %77) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %79 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %80 = "llvm.insertelement"(%78, %0, %79) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %81 = "llvm.mlir.constant"() <{value = 33554431 : i32}> : () -> i32
    %82 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %83 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %84 = "llvm.insertelement"(%82, %81, %83) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %85 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %86 = "llvm.insertelement"(%84, %0, %85) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %87 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %88 = "llvm.insertelement"(%86, %81, %87) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %89 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %90 = "llvm.insertelement"(%88, %0, %89) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %91 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %92 = "llvm.insertelement"(%90, %81, %91) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %93 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %94 = "llvm.insertelement"(%92, %0, %93) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %95 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %96 = "llvm.insertelement"(%94, %81, %95) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %97 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %98 = "llvm.insertelement"(%96, %0, %97) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %99 = "llvm.bitcast"(%arg0) : (vector<4xi64>) -> vector<8xi32>
    %100 = "llvm.shufflevector"(%99, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %101 = "llvm.shufflevector"(%99, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %102 = "llvm.bitcast"(%arg1) : (vector<4xi64>) -> vector<8xi32>
    %103 = "llvm.shufflevector"(%102, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %104 = "llvm.shufflevector"(%102, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %105 = "llvm.bitcast"(%103) : (vector<8xi32>) -> vector<4xi64>
    %106 = "llvm.bitcast"(%104) : (vector<8xi32>) -> vector<4xi64>
    %107 = "llvm.bitcast"(%arg2) : (vector<4xi64>) -> vector<8xi32>
    %108 = "llvm.shufflevector"(%107, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %109 = "llvm.shufflevector"(%107, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %110 = "llvm.bitcast"(%108) : (vector<8xi32>) -> vector<4xi64>
    %111 = "llvm.bitcast"(%109) : (vector<8xi32>) -> vector<4xi64>
    %112 = "llvm.bitcast"(%arg3) : (vector<4xi64>) -> vector<8xi32>
    %113 = "llvm.shufflevector"(%112, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %114 = "llvm.shufflevector"(%112, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %115 = "llvm.bitcast"(%113) : (vector<8xi32>) -> vector<4xi64>
    %116 = "llvm.bitcast"(%114) : (vector<8xi32>) -> vector<4xi64>
    %117 = "llvm.bitcast"(%arg4) : (vector<4xi64>) -> vector<8xi32>
    %118 = "llvm.shufflevector"(%117, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %119 = "llvm.shufflevector"(%117, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %120 = "llvm.bitcast"(%118) : (vector<8xi32>) -> vector<4xi64>
    %121 = "llvm.bitcast"(%119) : (vector<8xi32>) -> vector<4xi64>
    %122 = "llvm.shl"(%100, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %123 = "llvm.bitcast"(%122) : (vector<8xi32>) -> vector<4xi64>
    %124 = "llvm.shl"(%101, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %125 = "llvm.bitcast"(%124) : (vector<8xi32>) -> vector<4xi64>
    %126 = "llvm.shl"(%103, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %127 = "llvm.bitcast"(%126) : (vector<8xi32>) -> vector<4xi64>
    %128 = "llvm.shl"(%104, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %129 = "llvm.bitcast"(%128) : (vector<8xi32>) -> vector<4xi64>
    %130 = "llvm.shl"(%109, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %131 = "llvm.bitcast"(%130) : (vector<8xi32>) -> vector<4xi64>
    %132 = "llvm.shl"(%113, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %133 = "llvm.bitcast"(%132) : (vector<8xi32>) -> vector<4xi64>
    %134 = "llvm.shl"(%114, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %135 = "llvm.bitcast"(%134) : (vector<8xi32>) -> vector<4xi64>
    %136 = "llvm.mul"(%116, %37) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %137 = "llvm.mul"(%120, %37) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %138 = "llvm.mul"(%121, %37) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %139 = "llvm.and"(%137, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %140 = "llvm.and"(%138, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %141 = "llvm.and"(%136, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %142 = "llvm.mul"(%110, %123) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %143 = "llvm.mul"(%129, %125) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %144 = "llvm.mul"(%105, %105) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %145 = "llvm.mul"(%139, %133) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %146 = "llvm.mul"(%140, %131) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %147 = "llvm.mul"(%141, %116) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %148 = "llvm.add"(%146, %147) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %149 = "llvm.shl"(%148, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %150 = "llvm.add"(%142, %144) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %151 = "llvm.add"(%150, %143) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %152 = "llvm.add"(%151, %145) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %153 = "llvm.add"(%152, %149) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %154 = "llvm.mul"(%111, %123) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %155 = "llvm.mul"(%110, %125) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %156 = "llvm.add"(%155, %154) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %157 = "llvm.mul"(%127, %106) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %158 = "llvm.add"(%156, %157) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %159 = "llvm.mul"(%139, %135) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %160 = "llvm.add"(%158, %159) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %161 = "llvm.mul"(%140, %115) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %162 = "llvm.shl"(%161, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %163 = "llvm.add"(%160, %162) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %164 = "llvm.mul"(%115, %123) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %165 = "llvm.mul"(%131, %125) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %166 = "llvm.mul"(%110, %127) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %167 = "llvm.mul"(%129, %106) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %168 = "llvm.mul"(%139, %120) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %169 = "llvm.mul"(%140, %135) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %170 = "llvm.shl"(%169, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %171 = "llvm.add"(%167, %166) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %172 = "llvm.add"(%171, %164) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %173 = "llvm.add"(%172, %165) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %174 = "llvm.add"(%173, %168) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %175 = "llvm.add"(%174, %170) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %176 = "llvm.mul"(%116, %123) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %177 = "llvm.mul"(%115, %125) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %178 = "llvm.mul"(%111, %127) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %179 = "llvm.mul"(%110, %129) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %180 = "llvm.mul"(%140, %120) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %181 = "llvm.shl"(%180, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %182 = "llvm.add"(%179, %178) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %183 = "llvm.add"(%182, %176) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %184 = "llvm.add"(%183, %177) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %185 = "llvm.add"(%184, %181) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %186 = "llvm.sub"(%50, %153) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %187 = "llvm.shufflevector"(%153, %186) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %188 = "llvm.sub"(%60, %163) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %189 = "llvm.shufflevector"(%163, %188) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %190 = "llvm.sub"(%50, %175) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %191 = "llvm.shufflevector"(%175, %190) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %192 = "llvm.sub"(%60, %185) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %193 = "llvm.shufflevector"(%185, %192) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %194 = "llvm.lshr"(%187, %61) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %195 = "llvm.add"(%194, %189) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %196 = "llvm.lshr"(%195, %62) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %197 = "llvm.add"(%196, %191) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %198 = "llvm.lshr"(%197, %61) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %199 = "llvm.add"(%198, %193) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %200 = "llvm.bitcast"(%197) : (vector<4xi64>) -> vector<8xi32>
    %201 = "llvm.and"(%200, %80) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %202 = "llvm.bitcast"(%199) : (vector<4xi64>) -> vector<8xi32>
    %203 = "llvm.and"(%202, %98) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %204 = "llvm.shufflevector"(%201, %203) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %205 = "llvm.bitcast"(%204) : (vector<8xi32>) -> vector<4xi64>
    "llvm.return"(%205) : (vector<4xi64>) -> ()
}

mlir_def observe4 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.poison"() : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %2 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %3 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %4 = "llvm.insertelement"(%2, %1, %3) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %5 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %6 = "llvm.insertelement"(%4, %1, %5) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %7 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %8 = "llvm.insertelement"(%6, %0, %7) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %9 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %10 = "llvm.insertelement"(%8, %0, %9) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %11 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %12 = "llvm.insertelement"(%10, %1, %11) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %13 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %14 = "llvm.insertelement"(%12, %1, %13) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %15 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %16 = "llvm.insertelement"(%14, %0, %15) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %17 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %18 = "llvm.insertelement"(%16, %0, %17) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %19 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %20 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %21 = "llvm.insertelement"(%19, %0, %20) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %22 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %23 = "llvm.insertelement"(%21, %0, %22) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %24 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %25 = "llvm.insertelement"(%23, %1, %24) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %26 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %27 = "llvm.insertelement"(%25, %1, %26) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %28 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %29 = "llvm.insertelement"(%27, %0, %28) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %30 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %31 = "llvm.insertelement"(%29, %0, %30) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %32 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %33 = "llvm.insertelement"(%31, %1, %32) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %34 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %35 = "llvm.insertelement"(%33, %1, %34) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %36 = "llvm.mlir.constant"() <{value = dense<1> : vector<8xi32>}> : () -> vector<8xi32>
    %37 = "llvm.mlir.constant"() <{value = dense<19> : vector<4xi64>}> : () -> vector<4xi64>
    %38 = "llvm.mlir.constant"() <{value = dense<4294967295> : vector<4xi64>}> : () -> vector<4xi64>
    %39 = "llvm.mlir.constant"() <{value = dense<1> : vector<4xi64>}> : () -> vector<4xi64>
    %40 = "llvm.mlir.constant"() <{value = 9223371899415822336 : i64}> : () -> i64
    %41 = "llvm.mlir.poison"() : () -> i64
    %42 = "llvm.mlir.undef"() : () -> vector<4xi64>
    %43 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %44 = "llvm.insertelement"(%42, %41, %43) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %45 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %46 = "llvm.insertelement"(%44, %41, %45) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %47 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %48 = "llvm.insertelement"(%46, %41, %47) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %49 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %50 = "llvm.insertelement"(%48, %40, %49) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %51 = "llvm.mlir.constant"() <{value = 4611685880988434432 : i64}> : () -> i64
    %52 = "llvm.mlir.undef"() : () -> vector<4xi64>
    %53 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %54 = "llvm.insertelement"(%52, %41, %53) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %55 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %56 = "llvm.insertelement"(%54, %41, %55) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %57 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %58 = "llvm.insertelement"(%56, %41, %57) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %59 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %60 = "llvm.insertelement"(%58, %51, %59) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %61 = "llvm.mlir.constant"() <{value = dense<26> : vector<4xi64>}> : () -> vector<4xi64>
    %62 = "llvm.mlir.constant"() <{value = dense<25> : vector<4xi64>}> : () -> vector<4xi64>
    %63 = "llvm.mlir.constant"() <{value = 67108863 : i32}> : () -> i32
    %64 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %65 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %66 = "llvm.insertelement"(%64, %63, %65) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %67 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %68 = "llvm.insertelement"(%66, %0, %67) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %69 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %70 = "llvm.insertelement"(%68, %63, %69) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %71 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %72 = "llvm.insertelement"(%70, %0, %71) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %73 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %74 = "llvm.insertelement"(%72, %63, %73) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %75 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %76 = "llvm.insertelement"(%74, %0, %75) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %77 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %78 = "llvm.insertelement"(%76, %63, %77) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %79 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %80 = "llvm.insertelement"(%78, %0, %79) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %81 = "llvm.mlir.constant"() <{value = 33554431 : i32}> : () -> i32
    %82 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %83 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %84 = "llvm.insertelement"(%82, %81, %83) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %85 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %86 = "llvm.insertelement"(%84, %0, %85) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %87 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %88 = "llvm.insertelement"(%86, %81, %87) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %89 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %90 = "llvm.insertelement"(%88, %0, %89) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %91 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %92 = "llvm.insertelement"(%90, %81, %91) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %93 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %94 = "llvm.insertelement"(%92, %0, %93) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %95 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %96 = "llvm.insertelement"(%94, %81, %95) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %97 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %98 = "llvm.insertelement"(%96, %0, %97) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %99 = "llvm.bitcast"(%arg0) : (vector<4xi64>) -> vector<8xi32>
    %100 = "llvm.shufflevector"(%99, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %101 = "llvm.shufflevector"(%99, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %102 = "llvm.bitcast"(%arg1) : (vector<4xi64>) -> vector<8xi32>
    %103 = "llvm.shufflevector"(%102, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %104 = "llvm.shufflevector"(%102, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %105 = "llvm.bitcast"(%103) : (vector<8xi32>) -> vector<4xi64>
    %106 = "llvm.bitcast"(%104) : (vector<8xi32>) -> vector<4xi64>
    %107 = "llvm.bitcast"(%arg2) : (vector<4xi64>) -> vector<8xi32>
    %108 = "llvm.shufflevector"(%107, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %109 = "llvm.shufflevector"(%107, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %110 = "llvm.bitcast"(%108) : (vector<8xi32>) -> vector<4xi64>
    %111 = "llvm.bitcast"(%109) : (vector<8xi32>) -> vector<4xi64>
    %112 = "llvm.bitcast"(%arg3) : (vector<4xi64>) -> vector<8xi32>
    %113 = "llvm.shufflevector"(%112, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %114 = "llvm.shufflevector"(%112, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %115 = "llvm.bitcast"(%113) : (vector<8xi32>) -> vector<4xi64>
    %116 = "llvm.bitcast"(%114) : (vector<8xi32>) -> vector<4xi64>
    %117 = "llvm.bitcast"(%arg4) : (vector<4xi64>) -> vector<8xi32>
    %118 = "llvm.shufflevector"(%117, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %119 = "llvm.shufflevector"(%117, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %120 = "llvm.bitcast"(%118) : (vector<8xi32>) -> vector<4xi64>
    %121 = "llvm.bitcast"(%119) : (vector<8xi32>) -> vector<4xi64>
    %122 = "llvm.shl"(%100, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %123 = "llvm.bitcast"(%122) : (vector<8xi32>) -> vector<4xi64>
    %124 = "llvm.shl"(%101, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %125 = "llvm.bitcast"(%124) : (vector<8xi32>) -> vector<4xi64>
    %126 = "llvm.shl"(%103, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %127 = "llvm.bitcast"(%126) : (vector<8xi32>) -> vector<4xi64>
    %128 = "llvm.shl"(%104, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %129 = "llvm.bitcast"(%128) : (vector<8xi32>) -> vector<4xi64>
    %130 = "llvm.shl"(%108, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %131 = "llvm.bitcast"(%130) : (vector<8xi32>) -> vector<4xi64>
    %132 = "llvm.shl"(%109, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %133 = "llvm.bitcast"(%132) : (vector<8xi32>) -> vector<4xi64>
    %134 = "llvm.shl"(%113, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %135 = "llvm.bitcast"(%134) : (vector<8xi32>) -> vector<4xi64>
    %136 = "llvm.shl"(%114, %36) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %137 = "llvm.bitcast"(%136) : (vector<8xi32>) -> vector<4xi64>
    %138 = "llvm.mul"(%116, %37) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %139 = "llvm.mul"(%120, %37) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %140 = "llvm.mul"(%121, %37) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %141 = "llvm.and"(%139, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %142 = "llvm.and"(%140, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %143 = "llvm.and"(%138, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %144 = "llvm.mul"(%110, %123) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %145 = "llvm.mul"(%129, %125) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %146 = "llvm.mul"(%105, %105) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %147 = "llvm.mul"(%141, %135) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %148 = "llvm.mul"(%142, %133) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %149 = "llvm.mul"(%143, %116) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %150 = "llvm.add"(%148, %149) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %151 = "llvm.shl"(%150, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %152 = "llvm.add"(%144, %146) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %153 = "llvm.add"(%152, %145) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %154 = "llvm.add"(%153, %147) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %155 = "llvm.add"(%154, %151) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %156 = "llvm.mul"(%111, %123) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %157 = "llvm.mul"(%110, %125) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %158 = "llvm.add"(%157, %156) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %159 = "llvm.mul"(%127, %106) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %160 = "llvm.add"(%158, %159) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %161 = "llvm.mul"(%141, %137) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %162 = "llvm.add"(%160, %161) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %163 = "llvm.mul"(%142, %115) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %164 = "llvm.shl"(%163, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %165 = "llvm.add"(%162, %164) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %166 = "llvm.mul"(%115, %123) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %167 = "llvm.mul"(%133, %125) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %168 = "llvm.mul"(%110, %127) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %169 = "llvm.mul"(%129, %106) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %170 = "llvm.mul"(%141, %120) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %171 = "llvm.mul"(%142, %137) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %172 = "llvm.shl"(%171, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %173 = "llvm.add"(%169, %168) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %174 = "llvm.add"(%173, %166) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %175 = "llvm.add"(%174, %167) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %176 = "llvm.add"(%175, %170) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %177 = "llvm.add"(%176, %172) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %178 = "llvm.mul"(%116, %123) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %179 = "llvm.mul"(%115, %125) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %180 = "llvm.mul"(%111, %127) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %181 = "llvm.mul"(%110, %129) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %182 = "llvm.mul"(%142, %120) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %183 = "llvm.shl"(%182, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %184 = "llvm.add"(%181, %180) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %185 = "llvm.add"(%184, %178) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %186 = "llvm.add"(%185, %179) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %187 = "llvm.add"(%186, %183) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %188 = "llvm.mul"(%120, %123) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %189 = "llvm.mul"(%137, %125) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %190 = "llvm.mul"(%115, %127) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %191 = "llvm.mul"(%133, %129) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %192 = "llvm.mul"(%110, %110) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %193 = "llvm.mul"(%142, %121) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %194 = "llvm.shl"(%193, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %195 = "llvm.add"(%190, %192) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %196 = "llvm.add"(%195, %191) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %197 = "llvm.add"(%196, %188) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %198 = "llvm.add"(%197, %189) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %199 = "llvm.add"(%198, %194) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %200 = "llvm.mul"(%121, %123) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %201 = "llvm.mul"(%120, %125) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %202 = "llvm.mul"(%116, %127) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %203 = "llvm.mul"(%115, %129) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %204 = "llvm.mul"(%131, %111) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %205 = "llvm.add"(%203, %202) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %206 = "llvm.add"(%205, %204) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %207 = "llvm.add"(%206, %200) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %208 = "llvm.add"(%207, %201) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %209 = "llvm.sub"(%50, %155) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %210 = "llvm.shufflevector"(%155, %209) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %211 = "llvm.sub"(%60, %165) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %212 = "llvm.shufflevector"(%165, %211) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %213 = "llvm.sub"(%50, %177) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %214 = "llvm.shufflevector"(%177, %213) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %215 = "llvm.sub"(%60, %187) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %216 = "llvm.shufflevector"(%187, %215) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %217 = "llvm.sub"(%50, %199) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %218 = "llvm.shufflevector"(%199, %217) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %219 = "llvm.sub"(%60, %208) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %220 = "llvm.shufflevector"(%208, %219) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %221 = "llvm.lshr"(%210, %61) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %222 = "llvm.add"(%221, %212) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %223 = "llvm.lshr"(%222, %62) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %224 = "llvm.add"(%223, %214) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %225 = "llvm.lshr"(%224, %61) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %226 = "llvm.add"(%225, %216) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %227 = "llvm.lshr"(%226, %62) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %228 = "llvm.add"(%227, %218) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %229 = "llvm.lshr"(%228, %61) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %230 = "llvm.add"(%229, %220) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %231 = "llvm.bitcast"(%228) : (vector<4xi64>) -> vector<8xi32>
    %232 = "llvm.and"(%231, %80) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %233 = "llvm.bitcast"(%230) : (vector<4xi64>) -> vector<8xi32>
    %234 = "llvm.and"(%233, %98) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %235 = "llvm.shufflevector"(%232, %234) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %236 = "llvm.bitcast"(%235) : (vector<8xi32>) -> vector<4xi64>
    "llvm.return"(%236) : (vector<4xi64>) -> ()
}

end
end Agave.Ed25519.Avx2SquareNegateD

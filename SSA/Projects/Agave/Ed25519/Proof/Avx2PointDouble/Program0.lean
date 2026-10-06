module

public import SSA.Projects.RIR.Syntax.Elab

/-! Verbatim compiler-generated observation region for the pinned AVX2
`ExtendedPoint::double`. The source and LLVM inlining inputs are recorded in
the extraction manifest. This definition alone asserts no correctness. -/
namespace Agave.Ed25519.Avx2PointDouble
@[expose] public section

mlir_def observe0 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.poison"() : () -> vector<8xi32>
    %1 = "llvm.mlir.poison"() : () -> i32
    %2 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %3 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %4 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %5 = "llvm.insertelement"(%3, %2, %4) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %6 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %7 = "llvm.insertelement"(%5, %2, %6) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %8 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %9 = "llvm.insertelement"(%7, %1, %8) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %10 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %11 = "llvm.insertelement"(%9, %1, %10) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %12 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %13 = "llvm.insertelement"(%11, %2, %12) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %14 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %15 = "llvm.insertelement"(%13, %2, %14) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %16 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %17 = "llvm.insertelement"(%15, %1, %16) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %18 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %19 = "llvm.insertelement"(%17, %1, %18) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %20 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %21 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %22 = "llvm.insertelement"(%20, %1, %21) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %23 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %24 = "llvm.insertelement"(%22, %1, %23) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %25 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %26 = "llvm.insertelement"(%24, %2, %25) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %27 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %28 = "llvm.insertelement"(%26, %2, %27) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %29 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %30 = "llvm.insertelement"(%28, %1, %29) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %31 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %32 = "llvm.insertelement"(%30, %1, %31) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %33 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %34 = "llvm.insertelement"(%32, %2, %33) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %35 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %36 = "llvm.insertelement"(%34, %2, %35) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %37 = "llvm.mlir.constant"() <{value = dense<1> : vector<8xi32>}> : () -> vector<8xi32>
    %38 = "llvm.mlir.constant"() <{value = dense<19> : vector<4xi64>}> : () -> vector<4xi64>
    %39 = "llvm.mlir.constant"() <{value = dense<4294967295> : vector<4xi64>}> : () -> vector<4xi64>
    %40 = "llvm.mlir.constant"() <{value = dense<1> : vector<4xi64>}> : () -> vector<4xi64>
    %41 = "llvm.mlir.constant"() <{value = 9223369425514659840 : i64}> : () -> i64
    %42 = "llvm.mlir.poison"() : () -> i64
    %43 = "llvm.mlir.undef"() : () -> vector<4xi64>
    %44 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %45 = "llvm.insertelement"(%43, %42, %44) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %46 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %47 = "llvm.insertelement"(%45, %42, %46) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %48 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %49 = "llvm.insertelement"(%47, %42, %48) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %50 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %51 = "llvm.insertelement"(%49, %41, %50) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %52 = "llvm.mlir.constant"() <{value = 4611685880988434432 : i64}> : () -> i64
    %53 = "llvm.mlir.undef"() : () -> vector<4xi64>
    %54 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %55 = "llvm.insertelement"(%53, %42, %54) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %56 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %57 = "llvm.insertelement"(%55, %42, %56) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %58 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %59 = "llvm.insertelement"(%57, %42, %58) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %60 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %61 = "llvm.insertelement"(%59, %52, %60) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %62 = "llvm.mlir.constant"() <{value = 9223371899415822336 : i64}> : () -> i64
    %63 = "llvm.mlir.undef"() : () -> vector<4xi64>
    %64 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %65 = "llvm.insertelement"(%63, %42, %64) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %66 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %67 = "llvm.insertelement"(%65, %42, %66) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %68 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %69 = "llvm.insertelement"(%67, %42, %68) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %70 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %71 = "llvm.insertelement"(%69, %62, %70) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %72 = "llvm.mlir.constant"() <{value = dense<26> : vector<4xi64>}> : () -> vector<4xi64>
    %73 = "llvm.mlir.constant"() <{value = dense<67108863> : vector<4xi64>}> : () -> vector<4xi64>
    %74 = "llvm.mlir.constant"() <{value = dense<25> : vector<4xi64>}> : () -> vector<4xi64>
    %75 = "llvm.mlir.constant"() <{value = dense<33554431> : vector<4xi64>}> : () -> vector<4xi64>
    %76 = "llvm.mlir.constant"() <{value = dense<51> : vector<4xi64>}> : () -> vector<4xi64>
    %77 = "llvm.mlir.constant"() <{value = 67108863 : i32}> : () -> i32
    %78 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %79 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %80 = "llvm.insertelement"(%78, %77, %79) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %81 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %82 = "llvm.insertelement"(%80, %1, %81) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %83 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %84 = "llvm.insertelement"(%82, %77, %83) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %85 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %86 = "llvm.insertelement"(%84, %1, %85) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %87 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %88 = "llvm.insertelement"(%86, %77, %87) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %89 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %90 = "llvm.insertelement"(%88, %1, %89) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %91 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %92 = "llvm.insertelement"(%90, %77, %91) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %93 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %94 = "llvm.insertelement"(%92, %1, %93) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %95 = "llvm.mlir.constant"() <{value = 33554431 : i32}> : () -> i32
    %96 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %97 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %98 = "llvm.insertelement"(%96, %95, %97) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %99 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %100 = "llvm.insertelement"(%98, %1, %99) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %101 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %102 = "llvm.insertelement"(%100, %95, %101) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %103 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %104 = "llvm.insertelement"(%102, %1, %103) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %105 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %106 = "llvm.insertelement"(%104, %95, %105) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %107 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %108 = "llvm.insertelement"(%106, %1, %107) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %109 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %110 = "llvm.insertelement"(%108, %95, %109) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %111 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %112 = "llvm.insertelement"(%110, %1, %111) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %113 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %114 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %115 = "llvm.insertelement"(%113, %2, %114) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %116 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %117 = "llvm.insertelement"(%115, %2, %116) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %118 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %119 = "llvm.insertelement"(%117, %2, %118) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %120 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %121 = "llvm.insertelement"(%119, %2, %120) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %122 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %123 = "llvm.insertelement"(%121, %1, %122) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %124 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %125 = "llvm.insertelement"(%123, %1, %124) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %126 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %127 = "llvm.insertelement"(%125, %1, %126) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %128 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %129 = "llvm.insertelement"(%127, %1, %128) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %130 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %131 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %132 = "llvm.insertelement"(%130, %1, %131) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %133 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %134 = "llvm.insertelement"(%132, %2, %133) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %135 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %136 = "llvm.insertelement"(%134, %1, %135) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %137 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %138 = "llvm.insertelement"(%136, %2, %137) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %139 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %140 = "llvm.insertelement"(%138, %2, %139) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %141 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %142 = "llvm.insertelement"(%140, %1, %141) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %143 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %144 = "llvm.insertelement"(%142, %2, %143) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %145 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %146 = "llvm.insertelement"(%144, %1, %145) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %147 = "llvm.mlir.constant"() <{value = 67108862 : i32}> : () -> i32
    %148 = "llvm.mlir.constant"() <{value = 134217690 : i32}> : () -> i32
    %149 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %150 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %151 = "llvm.insertelement"(%149, %1, %150) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %152 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %153 = "llvm.insertelement"(%151, %148, %152) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %154 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %155 = "llvm.insertelement"(%153, %1, %154) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %156 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %157 = "llvm.insertelement"(%155, %147, %156) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %158 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %159 = "llvm.insertelement"(%157, %148, %158) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %160 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %161 = "llvm.insertelement"(%159, %1, %160) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %162 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %163 = "llvm.insertelement"(%161, %147, %162) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %164 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %165 = "llvm.insertelement"(%163, %1, %164) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %166 = "llvm.mlir.constant"() <{value = 134217726 : i32}> : () -> i32
    %167 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %168 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %169 = "llvm.insertelement"(%167, %1, %168) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %170 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %171 = "llvm.insertelement"(%169, %166, %170) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %172 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %173 = "llvm.insertelement"(%171, %1, %172) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %174 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %175 = "llvm.insertelement"(%173, %147, %174) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %176 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %177 = "llvm.insertelement"(%175, %166, %176) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %178 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %179 = "llvm.insertelement"(%177, %1, %178) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %180 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %181 = "llvm.insertelement"(%179, %147, %180) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %182 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %183 = "llvm.insertelement"(%181, %1, %182) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %184 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %185 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %186 = "llvm.insertelement"(%184, %2, %185) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %187 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %188 = "llvm.insertelement"(%186, %1, %187) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %189 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %190 = "llvm.insertelement"(%188, %2, %189) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %191 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %192 = "llvm.insertelement"(%190, %1, %191) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %193 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %194 = "llvm.insertelement"(%192, %1, %193) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %195 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %196 = "llvm.insertelement"(%194, %2, %195) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %197 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %198 = "llvm.insertelement"(%196, %1, %197) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %199 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %200 = "llvm.insertelement"(%198, %2, %199) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %201 = "llvm.bitcast"(%arg0) : (vector<4xi64>) -> vector<8xi32>
    %202 = "llvm.bitcast"(%arg1) : (vector<4xi64>) -> vector<8xi32>
    %203 = "llvm.bitcast"(%arg2) : (vector<4xi64>) -> vector<8xi32>
    %204 = "llvm.bitcast"(%arg3) : (vector<4xi64>) -> vector<8xi32>
    %205 = "llvm.shufflevector"(%201, %0) <{mask = array<i32: -1, -1, -1, -1, -1, 1, -1, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %206 = "llvm.shufflevector"(%202, %0) <{mask = array<i32: -1, -1, -1, -1, -1, 1, -1, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %207 = "llvm.shufflevector"(%203, %0) <{mask = array<i32: -1, -1, -1, -1, -1, 1, -1, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %208 = "llvm.shufflevector"(%204, %0) <{mask = array<i32: -1, -1, -1, -1, -1, 1, -1, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %209 = "llvm.bitcast"(%arg4) : (vector<4xi64>) -> vector<8xi32>
    %210 = "llvm.shufflevector"(%209, %0) <{mask = array<i32: -1, -1, -1, -1, -1, 1, -1, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %211 = "llvm.shufflevector"(%201, %0) <{mask = array<i32: -1, -1, -1, -1, -1, 0, -1, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %212 = "llvm.shufflevector"(%202, %0) <{mask = array<i32: -1, -1, -1, -1, -1, 0, -1, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %213 = "llvm.shufflevector"(%203, %0) <{mask = array<i32: -1, -1, -1, -1, -1, 0, -1, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %214 = "llvm.shufflevector"(%204, %0) <{mask = array<i32: -1, -1, -1, -1, -1, 0, -1, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %215 = "llvm.shufflevector"(%209, %0) <{mask = array<i32: -1, -1, -1, -1, -1, 0, -1, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %216 = "llvm.add"(%211, %205) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %217 = "llvm.add"(%212, %206) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %218 = "llvm.add"(%213, %207) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %219 = "llvm.add"(%214, %208) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %220 = "llvm.add"(%215, %210) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %221 = "llvm.shufflevector"(%201, %216) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %222 = "llvm.shufflevector"(%202, %217) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %223 = "llvm.shufflevector"(%203, %218) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %224 = "llvm.shufflevector"(%204, %219) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %225 = "llvm.shufflevector"(%209, %220) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %226 = "llvm.shufflevector"(%221, %19) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %227 = "llvm.shufflevector"(%221, %36) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %228 = "llvm.bitcast"(%226) : (vector<8xi32>) -> vector<4xi64>
    %229 = "llvm.bitcast"(%227) : (vector<8xi32>) -> vector<4xi64>
    %230 = "llvm.shufflevector"(%222, %19) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %231 = "llvm.shufflevector"(%222, %36) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %232 = "llvm.bitcast"(%230) : (vector<8xi32>) -> vector<4xi64>
    %233 = "llvm.bitcast"(%231) : (vector<8xi32>) -> vector<4xi64>
    %234 = "llvm.shufflevector"(%223, %19) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %235 = "llvm.shufflevector"(%223, %36) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %236 = "llvm.bitcast"(%234) : (vector<8xi32>) -> vector<4xi64>
    %237 = "llvm.bitcast"(%235) : (vector<8xi32>) -> vector<4xi64>
    %238 = "llvm.shufflevector"(%224, %19) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %239 = "llvm.shufflevector"(%224, %36) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %240 = "llvm.bitcast"(%238) : (vector<8xi32>) -> vector<4xi64>
    %241 = "llvm.bitcast"(%239) : (vector<8xi32>) -> vector<4xi64>
    %242 = "llvm.shufflevector"(%225, %19) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %243 = "llvm.shufflevector"(%225, %36) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %244 = "llvm.bitcast"(%242) : (vector<8xi32>) -> vector<4xi64>
    %245 = "llvm.bitcast"(%243) : (vector<8xi32>) -> vector<4xi64>
    %246 = "llvm.shl"(%226, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %247 = "llvm.bitcast"(%246) : (vector<8xi32>) -> vector<4xi64>
    %248 = "llvm.shl"(%227, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %249 = "llvm.bitcast"(%248) : (vector<8xi32>) -> vector<4xi64>
    %250 = "llvm.shl"(%230, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %251 = "llvm.bitcast"(%250) : (vector<8xi32>) -> vector<4xi64>
    %252 = "llvm.shl"(%231, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %253 = "llvm.bitcast"(%252) : (vector<8xi32>) -> vector<4xi64>
    %254 = "llvm.shl"(%234, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %255 = "llvm.bitcast"(%254) : (vector<8xi32>) -> vector<4xi64>
    %256 = "llvm.shl"(%235, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %257 = "llvm.bitcast"(%256) : (vector<8xi32>) -> vector<4xi64>
    %258 = "llvm.shl"(%238, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %259 = "llvm.bitcast"(%258) : (vector<8xi32>) -> vector<4xi64>
    %260 = "llvm.shl"(%239, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %261 = "llvm.bitcast"(%260) : (vector<8xi32>) -> vector<4xi64>
    %262 = "llvm.mul"(%237, %38) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %263 = "llvm.mul"(%240, %38) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %264 = "llvm.mul"(%241, %38) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %265 = "llvm.mul"(%244, %38) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %266 = "llvm.mul"(%245, %38) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %267 = "llvm.mul"(%228, %228) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %268 = "llvm.and"(%265, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %269 = "llvm.mul"(%268, %251) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %270 = "llvm.and"(%263, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %271 = "llvm.mul"(%270, %255) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %272 = "llvm.and"(%266, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %273 = "llvm.mul"(%272, %249) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %274 = "llvm.and"(%264, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %275 = "llvm.mul"(%274, %253) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %276 = "llvm.and"(%262, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %277 = "llvm.mul"(%276, %237) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %278 = "llvm.add"(%275, %277) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %279 = "llvm.add"(%278, %273) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %280 = "llvm.shl"(%279, %40) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %281 = "llvm.add"(%271, %267) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %282 = "llvm.add"(%281, %269) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %283 = "llvm.add"(%282, %280) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %284 = "llvm.mul"(%247, %229) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %285 = "llvm.mul"(%268, %253) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %286 = "llvm.mul"(%270, %257) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %287 = "llvm.mul"(%272, %232) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %288 = "llvm.mul"(%274, %236) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %289 = "llvm.add"(%287, %288) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %290 = "llvm.shl"(%289, %40) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %291 = "llvm.add"(%286, %284) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %292 = "llvm.add"(%291, %285) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %293 = "llvm.add"(%292, %290) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %294 = "llvm.mul"(%232, %247) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %295 = "llvm.mul"(%249, %229) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %296 = "llvm.add"(%295, %294) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %297 = "llvm.mul"(%268, %255) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %298 = "llvm.mul"(%270, %240) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %299 = "llvm.mul"(%272, %253) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %300 = "llvm.mul"(%274, %257) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %301 = "llvm.add"(%299, %300) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %302 = "llvm.shl"(%301, %40) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %303 = "llvm.add"(%296, %298) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %304 = "llvm.add"(%303, %297) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %305 = "llvm.add"(%304, %302) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %306 = "llvm.mul"(%233, %247) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %307 = "llvm.mul"(%232, %249) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %308 = "llvm.add"(%307, %306) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %309 = "llvm.mul"(%268, %257) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %310 = "llvm.add"(%308, %309) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %311 = "llvm.mul"(%272, %236) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %312 = "llvm.mul"(%274, %240) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %313 = "llvm.add"(%311, %312) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %314 = "llvm.shl"(%313, %40) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %315 = "llvm.add"(%310, %314) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %316 = "llvm.mul"(%236, %247) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %317 = "llvm.mul"(%253, %249) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %318 = "llvm.mul"(%232, %232) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %319 = "llvm.mul"(%268, %259) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %320 = "llvm.mul"(%272, %257) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %321 = "llvm.mul"(%274, %241) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %322 = "llvm.add"(%320, %321) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %323 = "llvm.shl"(%322, %40) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %324 = "llvm.add"(%316, %318) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %325 = "llvm.add"(%324, %317) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %326 = "llvm.add"(%325, %319) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %327 = "llvm.add"(%326, %323) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %328 = "llvm.mul"(%237, %247) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %329 = "llvm.mul"(%236, %249) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %330 = "llvm.add"(%329, %328) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %331 = "llvm.mul"(%251, %233) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %332 = "llvm.add"(%330, %331) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %333 = "llvm.mul"(%268, %261) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %334 = "llvm.add"(%332, %333) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %335 = "llvm.mul"(%272, %240) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %336 = "llvm.shl"(%335, %40) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %337 = "llvm.add"(%334, %336) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %338 = "llvm.mul"(%240, %247) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %339 = "llvm.mul"(%257, %249) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %340 = "llvm.mul"(%236, %251) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %341 = "llvm.mul"(%253, %233) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %342 = "llvm.mul"(%268, %244) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %343 = "llvm.mul"(%272, %261) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %344 = "llvm.shl"(%343, %40) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %345 = "llvm.add"(%341, %340) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %346 = "llvm.add"(%345, %338) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %347 = "llvm.add"(%346, %339) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %348 = "llvm.add"(%347, %342) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %349 = "llvm.add"(%348, %344) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %350 = "llvm.mul"(%241, %247) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %351 = "llvm.mul"(%240, %249) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %352 = "llvm.mul"(%237, %251) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %353 = "llvm.mul"(%236, %253) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %354 = "llvm.mul"(%272, %244) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %355 = "llvm.shl"(%354, %40) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %356 = "llvm.add"(%353, %352) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %357 = "llvm.add"(%356, %350) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %358 = "llvm.add"(%357, %351) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %359 = "llvm.add"(%358, %355) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %360 = "llvm.mul"(%244, %247) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %361 = "llvm.mul"(%261, %249) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %362 = "llvm.mul"(%240, %251) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %363 = "llvm.mul"(%257, %253) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %364 = "llvm.mul"(%236, %236) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %365 = "llvm.mul"(%272, %245) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %366 = "llvm.shl"(%365, %40) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %367 = "llvm.add"(%362, %364) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %368 = "llvm.add"(%367, %363) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %369 = "llvm.add"(%368, %360) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %370 = "llvm.add"(%369, %361) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %371 = "llvm.add"(%370, %366) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %372 = "llvm.mul"(%245, %247) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %373 = "llvm.mul"(%244, %249) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %374 = "llvm.mul"(%241, %251) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %375 = "llvm.mul"(%240, %253) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %376 = "llvm.mul"(%255, %237) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %377 = "llvm.add"(%375, %374) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %378 = "llvm.add"(%377, %376) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %379 = "llvm.add"(%378, %372) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %380 = "llvm.add"(%379, %373) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %381 = "llvm.sub"(%51, %283) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %382 = "llvm.shufflevector"(%283, %381) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %383 = "llvm.sub"(%61, %293) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %384 = "llvm.shufflevector"(%293, %383) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %385 = "llvm.sub"(%71, %305) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %386 = "llvm.shufflevector"(%305, %385) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %387 = "llvm.sub"(%61, %315) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %388 = "llvm.shufflevector"(%315, %387) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %389 = "llvm.sub"(%71, %327) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %390 = "llvm.shufflevector"(%327, %389) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %391 = "llvm.sub"(%61, %337) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %392 = "llvm.shufflevector"(%337, %391) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %393 = "llvm.sub"(%71, %349) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %394 = "llvm.shufflevector"(%349, %393) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %395 = "llvm.sub"(%61, %359) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %396 = "llvm.shufflevector"(%359, %395) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %397 = "llvm.sub"(%71, %371) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %398 = "llvm.shufflevector"(%371, %397) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %399 = "llvm.sub"(%61, %380) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %400 = "llvm.shufflevector"(%380, %399) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %401 = "llvm.lshr"(%382, %72) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %402 = "llvm.add"(%401, %384) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %403 = "llvm.and"(%382, %73) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %404 = "llvm.lshr"(%390, %72) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %405 = "llvm.add"(%404, %392) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %406 = "llvm.and"(%390, %73) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %407 = "llvm.lshr"(%402, %74) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %408 = "llvm.add"(%407, %386) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %409 = "llvm.and"(%402, %75) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %410 = "llvm.lshr"(%405, %74) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %411 = "llvm.add"(%410, %394) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %412 = "llvm.and"(%405, %75) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %413 = "llvm.lshr"(%408, %72) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %414 = "llvm.add"(%413, %388) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %415 = "llvm.lshr"(%411, %72) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %416 = "llvm.add"(%415, %396) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %417 = "llvm.lshr"(%414, %74) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %418 = "llvm.add"(%417, %406) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %419 = "llvm.lshr"(%416, %74) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %420 = "llvm.add"(%419, %398) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %421 = "llvm.lshr"(%418, %72) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %422 = "llvm.add"(%421, %412) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %423 = "llvm.lshr"(%420, %72) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %424 = "llvm.add"(%423, %400) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %425 = "llvm.lshr"(%424, %74) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %426 = "llvm.and"(%425, %73) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %427 = "llvm.lshr"(%424, %76) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %428 = "llvm.mul"(%426, %38) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %429 = "llvm.mul"(%427, %38) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %430 = "llvm.add"(%428, %403) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %431 = "llvm.add"(%429, %409) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %432 = "llvm.lshr"(%430, %72) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %433 = "llvm.add"(%431, %432) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %434 = "llvm.bitcast"(%430) : (vector<4xi64>) -> vector<8xi32>
    %435 = "llvm.and"(%434, %94) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %436 = "llvm.bitcast"(%433) : (vector<4xi64>) -> vector<8xi32>
    %437 = "llvm.shufflevector"(%435, %436) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %438 = "llvm.bitcast"(%408) : (vector<4xi64>) -> vector<8xi32>
    %439 = "llvm.and"(%438, %94) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %440 = "llvm.bitcast"(%414) : (vector<4xi64>) -> vector<8xi32>
    %441 = "llvm.and"(%440, %112) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %442 = "llvm.shufflevector"(%439, %441) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %443 = "llvm.bitcast"(%422) : (vector<4xi64>) -> vector<8xi32>
    %444 = "llvm.bitcast"(%418) : (vector<4xi64>) -> vector<8xi32>
    %445 = "llvm.and"(%444, %94) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %446 = "llvm.shufflevector"(%445, %443) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %447 = "llvm.bitcast"(%411) : (vector<4xi64>) -> vector<8xi32>
    %448 = "llvm.and"(%447, %94) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %449 = "llvm.bitcast"(%416) : (vector<4xi64>) -> vector<8xi32>
    %450 = "llvm.and"(%449, %112) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %451 = "llvm.shufflevector"(%448, %450) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %452 = "llvm.bitcast"(%420) : (vector<4xi64>) -> vector<8xi32>
    %453 = "llvm.and"(%452, %94) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %454 = "llvm.bitcast"(%424) : (vector<4xi64>) -> vector<8xi32>
    %455 = "llvm.and"(%454, %112) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %456 = "llvm.shufflevector"(%453, %455) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %457 = "llvm.shufflevector"(%437, %0) <{mask = array<i32: 0, 0, 2, 2, 0, 0, 2, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %458 = "llvm.shufflevector"(%442, %0) <{mask = array<i32: 0, 0, 2, 2, 0, 0, 2, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %459 = "llvm.shufflevector"(%446, %0) <{mask = array<i32: 0, 0, 2, 2, 0, 0, 2, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %460 = "llvm.shufflevector"(%451, %0) <{mask = array<i32: 0, 0, 2, 2, 0, 0, 2, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %461 = "llvm.shufflevector"(%456, %0) <{mask = array<i32: 0, 0, 2, 2, 0, 0, 2, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %462 = "llvm.shufflevector"(%437, %0) <{mask = array<i32: 1, 1, 3, 3, 1, 1, 3, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %463 = "llvm.shufflevector"(%442, %0) <{mask = array<i32: 1, 1, 3, 3, 1, 1, 3, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %464 = "llvm.shufflevector"(%446, %0) <{mask = array<i32: 1, 1, 3, 3, 1, 1, 3, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %465 = "llvm.shufflevector"(%451, %0) <{mask = array<i32: 1, 1, 3, 3, 1, 1, 3, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %466 = "llvm.shufflevector"(%456, %0) <{mask = array<i32: 1, 1, 3, 3, 1, 1, 3, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %467 = "llvm.shl"(%437, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %468 = "llvm.shl"(%442, %37) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %469 = "llvm.shl"(%446, %37) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %470 = "llvm.shl"(%451, %37) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %471 = "llvm.shl"(%456, %37) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %472 = "llvm.shufflevector"(%129, %467) <{mask = array<i32: 0, 1, 2, 3, 12, -1, 14, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %473 = "llvm.shufflevector"(%129, %468) <{mask = array<i32: 0, 1, 2, 3, 12, -1, 14, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %474 = "llvm.shufflevector"(%129, %469) <{mask = array<i32: 0, 1, 2, 3, 12, -1, 14, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %475 = "llvm.shufflevector"(%129, %470) <{mask = array<i32: 0, 1, 2, 3, 12, -1, 14, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %476 = "llvm.shufflevector"(%129, %471) <{mask = array<i32: 0, 1, 2, 3, 12, -1, 14, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %477 = "llvm.shufflevector"(%472, %437) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %478 = "llvm.shufflevector"(%473, %442) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %479 = "llvm.shufflevector"(%474, %446) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %480 = "llvm.shufflevector"(%475, %451) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %481 = "llvm.shufflevector"(%476, %456) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %482 = "llvm.shufflevector"(%462, %146) <{mask = array<i32: 0, 9, 2, 11, 12, 5, 14, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %483 = "llvm.shufflevector"(%463, %146) <{mask = array<i32: 0, 9, 2, 11, 12, 5, 14, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %484 = "llvm.shufflevector"(%464, %146) <{mask = array<i32: 0, 9, 2, 11, 12, 5, 14, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %485 = "llvm.shufflevector"(%465, %146) <{mask = array<i32: 0, 9, 2, 11, 12, 5, 14, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %486 = "llvm.shufflevector"(%466, %146) <{mask = array<i32: 0, 9, 2, 11, 12, 5, 14, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %487 = "llvm.sub"(%165, %462) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %488 = "llvm.sub"(%183, %463) <{overflowFlags = 1 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %489 = "llvm.sub"(%183, %464) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %490 = "llvm.sub"(%183, %465) <{overflowFlags = 1 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %491 = "llvm.sub"(%183, %466) <{overflowFlags = 1 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %492 = "llvm.shufflevector"(%200, %487) <{mask = array<i32: 0, 9, 2, 11, 12, 5, 14, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %493 = "llvm.shufflevector"(%200, %488) <{mask = array<i32: 0, 9, 2, 11, 12, 5, 14, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %494 = "llvm.shufflevector"(%200, %489) <{mask = array<i32: 0, 9, 2, 11, 12, 5, 14, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %495 = "llvm.shufflevector"(%200, %490) <{mask = array<i32: 0, 9, 2, 11, 12, 5, 14, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %496 = "llvm.shufflevector"(%200, %491) <{mask = array<i32: 0, 9, 2, 11, 12, 5, 14, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %497 = "llvm.add"(%482, %457) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %498 = "llvm.add"(%497, %477) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %499 = "llvm.add"(%498, %492) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %500 = "llvm.add"(%483, %458) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %501 = "llvm.add"(%500, %478) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %502 = "llvm.add"(%501, %493) <{overflowFlags = 1 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %503 = "llvm.add"(%484, %459) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %504 = "llvm.add"(%503, %479) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %505 = "llvm.add"(%504, %494) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %506 = "llvm.add"(%485, %460) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %507 = "llvm.add"(%506, %480) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %508 = "llvm.add"(%507, %495) <{overflowFlags = 1 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %509 = "llvm.add"(%486, %461) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %510 = "llvm.add"(%509, %481) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %511 = "llvm.add"(%510, %496) <{overflowFlags = 1 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %512 = "llvm.shufflevector"(%499, %0) <{mask = array<i32: 5, 1, 7, 3, 1, 5, 3, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %513 = "llvm.shufflevector"(%502, %0) <{mask = array<i32: 5, 1, 7, 3, 1, 5, 3, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %514 = "llvm.shufflevector"(%505, %0) <{mask = array<i32: 5, 1, 7, 3, 1, 5, 3, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %515 = "llvm.shufflevector"(%508, %0) <{mask = array<i32: 5, 1, 7, 3, 1, 5, 3, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %516 = "llvm.shufflevector"(%511, %0) <{mask = array<i32: 5, 1, 7, 3, 1, 5, 3, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %517 = "llvm.shufflevector"(%499, %0) <{mask = array<i32: 4, 0, 6, 2, 4, 0, 6, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %518 = "llvm.shufflevector"(%502, %0) <{mask = array<i32: 4, 0, 6, 2, 4, 0, 6, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %519 = "llvm.shufflevector"(%505, %0) <{mask = array<i32: 4, 0, 6, 2, 4, 0, 6, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %520 = "llvm.shufflevector"(%508, %0) <{mask = array<i32: 4, 0, 6, 2, 4, 0, 6, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %521 = "llvm.shufflevector"(%511, %0) <{mask = array<i32: 4, 0, 6, 2, 4, 0, 6, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %522 = "llvm.shufflevector"(%517, %19) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %523 = "llvm.shufflevector"(%517, %36) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %524 = "llvm.bitcast"(%522) : (vector<8xi32>) -> vector<4xi64>
    %525 = "llvm.bitcast"(%523) : (vector<8xi32>) -> vector<4xi64>
    %526 = "llvm.shufflevector"(%518, %19) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %527 = "llvm.shufflevector"(%518, %36) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %528 = "llvm.bitcast"(%526) : (vector<8xi32>) -> vector<4xi64>
    %529 = "llvm.bitcast"(%527) : (vector<8xi32>) -> vector<4xi64>
    %530 = "llvm.shufflevector"(%519, %19) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %531 = "llvm.shufflevector"(%519, %36) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %532 = "llvm.bitcast"(%530) : (vector<8xi32>) -> vector<4xi64>
    %533 = "llvm.bitcast"(%531) : (vector<8xi32>) -> vector<4xi64>
    %534 = "llvm.shufflevector"(%520, %19) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %535 = "llvm.shufflevector"(%520, %36) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %536 = "llvm.bitcast"(%534) : (vector<8xi32>) -> vector<4xi64>
    %537 = "llvm.bitcast"(%535) : (vector<8xi32>) -> vector<4xi64>
    %538 = "llvm.shufflevector"(%521, %19) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %539 = "llvm.shufflevector"(%521, %36) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %540 = "llvm.bitcast"(%538) : (vector<8xi32>) -> vector<4xi64>
    %541 = "llvm.bitcast"(%539) : (vector<8xi32>) -> vector<4xi64>
    %542 = "llvm.shufflevector"(%512, %19) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %543 = "llvm.shufflevector"(%512, %36) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %544 = "llvm.bitcast"(%542) : (vector<8xi32>) -> vector<4xi64>
    %545 = "llvm.bitcast"(%543) : (vector<8xi32>) -> vector<4xi64>
    %546 = "llvm.shufflevector"(%513, %19) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %547 = "llvm.shufflevector"(%513, %36) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %548 = "llvm.bitcast"(%546) : (vector<8xi32>) -> vector<4xi64>
    %549 = "llvm.bitcast"(%547) : (vector<8xi32>) -> vector<4xi64>
    %550 = "llvm.shufflevector"(%514, %19) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %551 = "llvm.shufflevector"(%514, %36) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %552 = "llvm.bitcast"(%550) : (vector<8xi32>) -> vector<4xi64>
    %553 = "llvm.bitcast"(%551) : (vector<8xi32>) -> vector<4xi64>
    %554 = "llvm.shufflevector"(%515, %19) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %555 = "llvm.shufflevector"(%515, %36) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %556 = "llvm.bitcast"(%554) : (vector<8xi32>) -> vector<4xi64>
    %557 = "llvm.bitcast"(%555) : (vector<8xi32>) -> vector<4xi64>
    %558 = "llvm.shufflevector"(%516, %19) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %559 = "llvm.shufflevector"(%516, %36) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %560 = "llvm.bitcast"(%558) : (vector<8xi32>) -> vector<4xi64>
    %561 = "llvm.bitcast"(%559) : (vector<8xi32>) -> vector<4xi64>
    %562 = "llvm.mul"(%545, %38) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %563 = "llvm.mul"(%548, %38) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %564 = "llvm.mul"(%549, %38) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %565 = "llvm.mul"(%552, %38) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %566 = "llvm.mul"(%553, %38) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %567 = "llvm.mul"(%556, %38) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %568 = "llvm.mul"(%557, %38) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %569 = "llvm.mul"(%560, %38) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %570 = "llvm.mul"(%561, %38) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %571 = "llvm.mul"(%544, %524) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %572 = "llvm.shl"(%523, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %573 = "llvm.bitcast"(%572) : (vector<8xi32>) -> vector<4xi64>
    %574 = "llvm.and"(%570, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %575 = "llvm.mul"(%574, %573) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %576 = "llvm.and"(%569, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %577 = "llvm.mul"(%576, %528) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %578 = "llvm.shl"(%527, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %579 = "llvm.bitcast"(%578) : (vector<8xi32>) -> vector<4xi64>
    %580 = "llvm.and"(%568, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %581 = "llvm.mul"(%580, %579) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %582 = "llvm.and"(%567, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %583 = "llvm.mul"(%582, %532) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %584 = "llvm.shl"(%531, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %585 = "llvm.bitcast"(%584) : (vector<8xi32>) -> vector<4xi64>
    %586 = "llvm.and"(%566, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %587 = "llvm.mul"(%586, %585) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %588 = "llvm.and"(%565, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %589 = "llvm.mul"(%588, %536) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %590 = "llvm.shl"(%535, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %591 = "llvm.bitcast"(%590) : (vector<8xi32>) -> vector<4xi64>
    %592 = "llvm.and"(%564, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %593 = "llvm.mul"(%592, %591) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %594 = "llvm.and"(%563, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %595 = "llvm.mul"(%594, %540) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %596 = "llvm.shl"(%539, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %597 = "llvm.bitcast"(%596) : (vector<8xi32>) -> vector<4xi64>
    %598 = "llvm.and"(%562, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %599 = "llvm.mul"(%598, %597) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %600 = "llvm.add"(%599, %571) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %601 = "llvm.add"(%600, %595) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %602 = "llvm.add"(%601, %593) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %603 = "llvm.add"(%602, %589) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %604 = "llvm.add"(%603, %587) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %605 = "llvm.add"(%604, %583) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %606 = "llvm.add"(%605, %581) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %607 = "llvm.add"(%606, %577) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %608 = "llvm.add"(%607, %575) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %609 = "llvm.mul"(%545, %524) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %610 = "llvm.mul"(%544, %525) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %611 = "llvm.mul"(%570, %528) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %612 = "llvm.mul"(%569, %529) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %613 = "llvm.mul"(%580, %532) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %614 = "llvm.mul"(%582, %533) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %615 = "llvm.mul"(%586, %536) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %616 = "llvm.mul"(%588, %537) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %617 = "llvm.mul"(%592, %540) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %618 = "llvm.mul"(%594, %541) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %619 = "llvm.mul"(%552, %524) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %620 = "llvm.mul"(%549, %573) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %621 = "llvm.mul"(%548, %528) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %622 = "llvm.mul"(%545, %579) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %623 = "llvm.mul"(%544, %532) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %624 = "llvm.mul"(%574, %585) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %625 = "llvm.mul"(%576, %536) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %626 = "llvm.mul"(%580, %591) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %627 = "llvm.mul"(%582, %540) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %628 = "llvm.mul"(%586, %597) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %629 = "llvm.add"(%623, %622) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %630 = "llvm.add"(%629, %621) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %631 = "llvm.add"(%630, %620) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %632 = "llvm.add"(%631, %619) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %633 = "llvm.add"(%632, %628) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %634 = "llvm.add"(%633, %627) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %635 = "llvm.add"(%634, %626) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %636 = "llvm.add"(%635, %625) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %637 = "llvm.add"(%636, %624) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %638 = "llvm.mul"(%553, %524) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %639 = "llvm.mul"(%552, %525) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %640 = "llvm.mul"(%549, %528) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %641 = "llvm.mul"(%548, %529) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %642 = "llvm.mul"(%545, %532) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %643 = "llvm.mul"(%544, %533) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %644 = "llvm.mul"(%574, %536) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %645 = "llvm.mul"(%576, %537) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %646 = "llvm.mul"(%580, %540) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %647 = "llvm.mul"(%582, %541) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %648 = "llvm.mul"(%556, %524) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %649 = "llvm.mul"(%553, %573) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %650 = "llvm.mul"(%552, %528) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %651 = "llvm.mul"(%549, %579) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %652 = "llvm.mul"(%548, %532) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %653 = "llvm.mul"(%545, %585) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %654 = "llvm.mul"(%544, %536) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %655 = "llvm.mul"(%574, %591) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %656 = "llvm.mul"(%576, %540) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %657 = "llvm.mul"(%580, %597) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %658 = "llvm.mul"(%557, %524) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %659 = "llvm.mul"(%556, %525) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %660 = "llvm.mul"(%553, %528) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %661 = "llvm.mul"(%552, %529) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %662 = "llvm.mul"(%549, %532) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %663 = "llvm.mul"(%548, %533) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %664 = "llvm.mul"(%545, %536) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %665 = "llvm.mul"(%544, %537) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %666 = "llvm.mul"(%574, %540) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %667 = "llvm.mul"(%576, %541) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %668 = "llvm.mul"(%560, %524) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %669 = "llvm.mul"(%557, %573) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %670 = "llvm.mul"(%556, %528) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %671 = "llvm.mul"(%553, %579) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %672 = "llvm.mul"(%552, %532) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %673 = "llvm.mul"(%549, %585) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %674 = "llvm.mul"(%548, %536) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %675 = "llvm.mul"(%545, %591) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %676 = "llvm.mul"(%544, %540) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %677 = "llvm.mul"(%574, %597) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %678 = "llvm.mul"(%561, %524) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %679 = "llvm.mul"(%560, %525) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %680 = "llvm.mul"(%557, %528) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %681 = "llvm.mul"(%556, %529) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %682 = "llvm.mul"(%553, %532) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %683 = "llvm.mul"(%552, %533) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %684 = "llvm.mul"(%549, %536) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %685 = "llvm.mul"(%548, %537) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %686 = "llvm.mul"(%545, %540) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %687 = "llvm.mul"(%544, %541) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %688 = "llvm.lshr"(%608, %72) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %689 = "llvm.add"(%610, %609) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %690 = "llvm.add"(%689, %617) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %691 = "llvm.add"(%690, %618) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %692 = "llvm.add"(%691, %615) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %693 = "llvm.add"(%692, %616) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %694 = "llvm.add"(%693, %613) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %695 = "llvm.add"(%694, %614) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %696 = "llvm.add"(%695, %611) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %697 = "llvm.add"(%696, %612) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %698 = "llvm.add"(%697, %688) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %699 = "llvm.and"(%608, %73) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %700 = "llvm.lshr"(%637, %72) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %701 = "llvm.add"(%643, %642) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %702 = "llvm.add"(%701, %640) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %703 = "llvm.add"(%702, %641) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %704 = "llvm.add"(%703, %638) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %705 = "llvm.add"(%704, %639) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %706 = "llvm.add"(%705, %646) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %707 = "llvm.add"(%706, %647) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %708 = "llvm.add"(%707, %644) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %709 = "llvm.add"(%708, %645) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %710 = "llvm.add"(%709, %700) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %711 = "llvm.and"(%698, %75) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %712 = "llvm.lshr"(%710, %74) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %713 = "llvm.add"(%654, %653) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %714 = "llvm.add"(%713, %651) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %715 = "llvm.add"(%714, %652) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %716 = "llvm.add"(%715, %650) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %717 = "llvm.add"(%716, %649) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %718 = "llvm.add"(%717, %648) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %719 = "llvm.add"(%718, %657) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %720 = "llvm.add"(%719, %656) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %721 = "llvm.add"(%720, %655) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %722 = "llvm.add"(%721, %712) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %723 = "llvm.lshr"(%722, %72) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %724 = "llvm.add"(%665, %664) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %725 = "llvm.add"(%724, %662) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %726 = "llvm.add"(%725, %663) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %727 = "llvm.add"(%726, %660) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %728 = "llvm.add"(%727, %661) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %729 = "llvm.add"(%728, %658) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %730 = "llvm.add"(%729, %659) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %731 = "llvm.add"(%730, %666) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %732 = "llvm.add"(%731, %667) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %733 = "llvm.add"(%732, %723) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %734 = "llvm.lshr"(%733, %74) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %735 = "llvm.add"(%675, %676) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %736 = "llvm.add"(%735, %674) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %737 = "llvm.add"(%736, %673) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %738 = "llvm.add"(%737, %672) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %739 = "llvm.add"(%738, %671) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %740 = "llvm.add"(%739, %670) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %741 = "llvm.add"(%740, %669) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %742 = "llvm.add"(%741, %668) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %743 = "llvm.add"(%742, %677) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %744 = "llvm.add"(%743, %734) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %745 = "llvm.lshr"(%744, %72) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %746 = "llvm.add"(%687, %686) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %747 = "llvm.add"(%746, %684) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %748 = "llvm.add"(%747, %685) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %749 = "llvm.add"(%748, %682) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %750 = "llvm.add"(%749, %683) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %751 = "llvm.add"(%750, %680) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %752 = "llvm.add"(%751, %681) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %753 = "llvm.add"(%752, %678) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %754 = "llvm.add"(%753, %679) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %755 = "llvm.add"(%754, %745) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %756 = "llvm.lshr"(%755, %74) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %757 = "llvm.and"(%756, %73) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %758 = "llvm.lshr"(%755, %76) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %759 = "llvm.mul"(%757, %38) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %760 = "llvm.mul"(%758, %38) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %761 = "llvm.add"(%759, %699) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %762 = "llvm.add"(%760, %711) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %763 = "llvm.lshr"(%761, %72) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %764 = "llvm.add"(%762, %763) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %765 = "llvm.bitcast"(%761) : (vector<4xi64>) -> vector<8xi32>
    %766 = "llvm.and"(%765, %94) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %767 = "llvm.bitcast"(%764) : (vector<4xi64>) -> vector<8xi32>
    %768 = "llvm.shufflevector"(%766, %767) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %769 = "llvm.bitcast"(%768) : (vector<8xi32>) -> vector<4xi64>
    "llvm.return"(%769) : (vector<4xi64>) -> ()
}

end
end Agave.Ed25519.Avx2PointDouble

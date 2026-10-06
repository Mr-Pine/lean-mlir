"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<vector<4xi64> (vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], sym_name = "agave_avx2_field_mul_observe_1", target_cpu = "x86-64", target_features = #llvm.target_features<["+avx", "+avx2", "+sse", "+sse2", "+sse3", "+sse4.1", "+sse4.2", "+crc32", "+ssse3"]>, unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>, %arg5: vector<4xi64>, %arg6: vector<4xi64>, %arg7: vector<4xi64>, %arg8: vector<4xi64>, %arg9: vector<4xi64>):
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
    %36 = "llvm.mlir.constant"() <{value = dense<19> : vector<4xi64>}> : () -> vector<4xi64>
    %37 = "llvm.mlir.constant"() <{value = dense<1> : vector<8xi32>}> : () -> vector<8xi32>
    %38 = "llvm.mlir.constant"() <{value = dense<4294967295> : vector<4xi64>}> : () -> vector<4xi64>
    %39 = "llvm.mlir.constant"() <{value = dense<26> : vector<4xi64>}> : () -> vector<4xi64>
    %40 = "llvm.mlir.constant"() <{value = dense<25> : vector<4xi64>}> : () -> vector<4xi64>
    %41 = "llvm.mlir.constant"() <{value = 67108863 : i32}> : () -> i32
    %42 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %43 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %44 = "llvm.insertelement"(%42, %41, %43) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %45 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %46 = "llvm.insertelement"(%44, %0, %45) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %47 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %48 = "llvm.insertelement"(%46, %41, %47) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %49 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %50 = "llvm.insertelement"(%48, %0, %49) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %51 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %52 = "llvm.insertelement"(%50, %41, %51) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %53 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %54 = "llvm.insertelement"(%52, %0, %53) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %55 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %56 = "llvm.insertelement"(%54, %41, %55) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %57 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %58 = "llvm.insertelement"(%56, %0, %57) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %59 = "llvm.mlir.constant"() <{value = 33554431 : i32}> : () -> i32
    %60 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %61 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %62 = "llvm.insertelement"(%60, %59, %61) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %63 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %64 = "llvm.insertelement"(%62, %0, %63) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %65 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %66 = "llvm.insertelement"(%64, %59, %65) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %67 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %68 = "llvm.insertelement"(%66, %0, %67) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %69 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %70 = "llvm.insertelement"(%68, %59, %69) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %71 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %72 = "llvm.insertelement"(%70, %0, %71) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %73 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %74 = "llvm.insertelement"(%72, %59, %73) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %75 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %76 = "llvm.insertelement"(%74, %0, %75) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %77 = "llvm.bitcast"(%arg0) : (vector<4xi64>) -> vector<8xi32>
    %78 = "llvm.shufflevector"(%77, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %79 = "llvm.shufflevector"(%77, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %80 = "llvm.bitcast"(%78) : (vector<8xi32>) -> vector<4xi64>
    %81 = "llvm.bitcast"(%79) : (vector<8xi32>) -> vector<4xi64>
    %82 = "llvm.bitcast"(%arg1) : (vector<4xi64>) -> vector<8xi32>
    %83 = "llvm.shufflevector"(%82, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %84 = "llvm.shufflevector"(%82, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %85 = "llvm.bitcast"(%83) : (vector<8xi32>) -> vector<4xi64>
    %86 = "llvm.bitcast"(%84) : (vector<8xi32>) -> vector<4xi64>
    %87 = "llvm.bitcast"(%arg2) : (vector<4xi64>) -> vector<8xi32>
    %88 = "llvm.shufflevector"(%87, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %89 = "llvm.shufflevector"(%87, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %90 = "llvm.bitcast"(%88) : (vector<8xi32>) -> vector<4xi64>
    %91 = "llvm.bitcast"(%89) : (vector<8xi32>) -> vector<4xi64>
    %92 = "llvm.bitcast"(%arg3) : (vector<4xi64>) -> vector<8xi32>
    %93 = "llvm.shufflevector"(%92, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %94 = "llvm.shufflevector"(%92, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %95 = "llvm.bitcast"(%93) : (vector<8xi32>) -> vector<4xi64>
    %96 = "llvm.bitcast"(%94) : (vector<8xi32>) -> vector<4xi64>
    %97 = "llvm.bitcast"(%arg4) : (vector<4xi64>) -> vector<8xi32>
    %98 = "llvm.shufflevector"(%97, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %99 = "llvm.shufflevector"(%97, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %100 = "llvm.bitcast"(%98) : (vector<8xi32>) -> vector<4xi64>
    %101 = "llvm.bitcast"(%99) : (vector<8xi32>) -> vector<4xi64>
    %102 = "llvm.bitcast"(%arg5) : (vector<4xi64>) -> vector<8xi32>
    %103 = "llvm.shufflevector"(%102, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %104 = "llvm.shufflevector"(%102, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %105 = "llvm.bitcast"(%103) : (vector<8xi32>) -> vector<4xi64>
    %106 = "llvm.bitcast"(%104) : (vector<8xi32>) -> vector<4xi64>
    %107 = "llvm.bitcast"(%arg6) : (vector<4xi64>) -> vector<8xi32>
    %108 = "llvm.shufflevector"(%107, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %109 = "llvm.shufflevector"(%107, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %110 = "llvm.bitcast"(%108) : (vector<8xi32>) -> vector<4xi64>
    %111 = "llvm.bitcast"(%109) : (vector<8xi32>) -> vector<4xi64>
    %112 = "llvm.bitcast"(%arg7) : (vector<4xi64>) -> vector<8xi32>
    %113 = "llvm.shufflevector"(%112, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %114 = "llvm.shufflevector"(%112, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %115 = "llvm.bitcast"(%113) : (vector<8xi32>) -> vector<4xi64>
    %116 = "llvm.bitcast"(%114) : (vector<8xi32>) -> vector<4xi64>
    %117 = "llvm.bitcast"(%arg8) : (vector<4xi64>) -> vector<8xi32>
    %118 = "llvm.shufflevector"(%117, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %119 = "llvm.shufflevector"(%117, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %120 = "llvm.bitcast"(%118) : (vector<8xi32>) -> vector<4xi64>
    %121 = "llvm.bitcast"(%119) : (vector<8xi32>) -> vector<4xi64>
    %122 = "llvm.bitcast"(%arg9) : (vector<4xi64>) -> vector<8xi32>
    %123 = "llvm.shufflevector"(%122, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %124 = "llvm.shufflevector"(%122, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %125 = "llvm.bitcast"(%123) : (vector<8xi32>) -> vector<4xi64>
    %126 = "llvm.bitcast"(%124) : (vector<8xi32>) -> vector<4xi64>
    %127 = "llvm.mul"(%106, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %128 = "llvm.mul"(%110, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %129 = "llvm.mul"(%111, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %130 = "llvm.mul"(%115, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %131 = "llvm.mul"(%116, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %132 = "llvm.mul"(%120, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %133 = "llvm.mul"(%121, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %134 = "llvm.mul"(%125, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %135 = "llvm.mul"(%126, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %136 = "llvm.mul"(%105, %80) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %137 = "llvm.shl"(%79, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %138 = "llvm.bitcast"(%137) : (vector<8xi32>) -> vector<4xi64>
    %139 = "llvm.and"(%135, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %140 = "llvm.mul"(%139, %138) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %141 = "llvm.and"(%134, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %142 = "llvm.mul"(%141, %85) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %143 = "llvm.shl"(%84, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %144 = "llvm.bitcast"(%143) : (vector<8xi32>) -> vector<4xi64>
    %145 = "llvm.and"(%133, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %146 = "llvm.mul"(%145, %144) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %147 = "llvm.and"(%132, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %148 = "llvm.mul"(%147, %90) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %149 = "llvm.shl"(%89, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %150 = "llvm.bitcast"(%149) : (vector<8xi32>) -> vector<4xi64>
    %151 = "llvm.and"(%131, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %152 = "llvm.mul"(%151, %150) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %153 = "llvm.and"(%130, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %154 = "llvm.mul"(%153, %95) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %155 = "llvm.shl"(%94, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %156 = "llvm.bitcast"(%155) : (vector<8xi32>) -> vector<4xi64>
    %157 = "llvm.and"(%129, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %158 = "llvm.mul"(%157, %156) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %159 = "llvm.and"(%128, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %160 = "llvm.mul"(%159, %100) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %161 = "llvm.shl"(%99, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %162 = "llvm.bitcast"(%161) : (vector<8xi32>) -> vector<4xi64>
    %163 = "llvm.and"(%127, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %164 = "llvm.mul"(%163, %162) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %165 = "llvm.add"(%164, %136) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %166 = "llvm.add"(%165, %160) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %167 = "llvm.add"(%166, %158) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %168 = "llvm.add"(%167, %154) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %169 = "llvm.add"(%168, %152) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %170 = "llvm.add"(%169, %148) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %171 = "llvm.add"(%170, %146) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %172 = "llvm.add"(%171, %142) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %173 = "llvm.add"(%172, %140) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %174 = "llvm.mul"(%106, %80) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %175 = "llvm.mul"(%105, %81) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %176 = "llvm.mul"(%139, %85) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %177 = "llvm.mul"(%141, %86) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %178 = "llvm.mul"(%145, %90) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %179 = "llvm.mul"(%147, %91) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %180 = "llvm.mul"(%151, %95) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %181 = "llvm.mul"(%153, %96) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %182 = "llvm.mul"(%157, %100) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %183 = "llvm.mul"(%159, %101) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %184 = "llvm.mul"(%110, %80) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %185 = "llvm.mul"(%106, %138) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %186 = "llvm.mul"(%105, %85) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %187 = "llvm.mul"(%139, %144) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %188 = "llvm.mul"(%141, %90) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %189 = "llvm.mul"(%145, %150) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %190 = "llvm.mul"(%147, %95) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %191 = "llvm.mul"(%151, %156) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %192 = "llvm.mul"(%153, %100) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %193 = "llvm.mul"(%157, %162) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %194 = "llvm.mul"(%111, %80) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %195 = "llvm.mul"(%110, %81) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %196 = "llvm.mul"(%106, %85) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %197 = "llvm.mul"(%105, %86) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %198 = "llvm.mul"(%139, %90) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %199 = "llvm.mul"(%141, %91) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %200 = "llvm.mul"(%145, %95) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %201 = "llvm.mul"(%147, %96) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %202 = "llvm.mul"(%151, %100) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %203 = "llvm.mul"(%153, %101) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %204 = "llvm.lshr"(%173, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %205 = "llvm.add"(%175, %174) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %206 = "llvm.add"(%205, %182) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %207 = "llvm.add"(%206, %183) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %208 = "llvm.add"(%207, %180) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %209 = "llvm.add"(%208, %181) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %210 = "llvm.add"(%209, %178) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %211 = "llvm.add"(%210, %179) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %212 = "llvm.add"(%211, %176) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %213 = "llvm.add"(%212, %177) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %214 = "llvm.add"(%213, %204) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %215 = "llvm.lshr"(%214, %40) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %216 = "llvm.add"(%186, %185) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %217 = "llvm.add"(%216, %184) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %218 = "llvm.add"(%217, %193) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %219 = "llvm.add"(%218, %192) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %220 = "llvm.add"(%219, %191) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %221 = "llvm.add"(%220, %190) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %222 = "llvm.add"(%221, %189) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %223 = "llvm.add"(%222, %188) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %224 = "llvm.add"(%223, %187) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %225 = "llvm.add"(%224, %215) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %226 = "llvm.lshr"(%225, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %227 = "llvm.add"(%197, %196) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %228 = "llvm.add"(%227, %194) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %229 = "llvm.add"(%228, %195) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %230 = "llvm.add"(%229, %202) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %231 = "llvm.add"(%230, %203) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %232 = "llvm.add"(%231, %200) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %233 = "llvm.add"(%232, %201) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %234 = "llvm.add"(%233, %198) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %235 = "llvm.add"(%234, %199) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %236 = "llvm.add"(%235, %226) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %237 = "llvm.bitcast"(%225) : (vector<4xi64>) -> vector<8xi32>
    %238 = "llvm.and"(%237, %58) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %239 = "llvm.bitcast"(%236) : (vector<4xi64>) -> vector<8xi32>
    %240 = "llvm.and"(%239, %76) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %241 = "llvm.shufflevector"(%238, %240) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %242 = "llvm.bitcast"(%241) : (vector<8xi32>) -> vector<4xi64>
    "llvm.return"(%242) : (vector<4xi64>) -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<vector<4xi64> (vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], sym_name = "agave_avx2_field_mul_observe_3", target_cpu = "x86-64", target_features = #llvm.target_features<["+avx", "+avx2", "+sse", "+sse2", "+sse3", "+sse4.1", "+sse4.2", "+crc32", "+ssse3"]>, unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
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
    %127 = "llvm.mul"(%116, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %128 = "llvm.mul"(%120, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %129 = "llvm.mul"(%121, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %130 = "llvm.mul"(%125, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %131 = "llvm.mul"(%126, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %132 = "llvm.shl"(%79, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %133 = "llvm.bitcast"(%132) : (vector<8xi32>) -> vector<4xi64>
    %134 = "llvm.and"(%131, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %135 = "llvm.and"(%130, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %136 = "llvm.shl"(%84, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %137 = "llvm.bitcast"(%136) : (vector<8xi32>) -> vector<4xi64>
    %138 = "llvm.and"(%129, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %139 = "llvm.and"(%128, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %140 = "llvm.shl"(%89, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %141 = "llvm.bitcast"(%140) : (vector<8xi32>) -> vector<4xi64>
    %142 = "llvm.and"(%127, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %143 = "llvm.shl"(%94, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %144 = "llvm.bitcast"(%143) : (vector<8xi32>) -> vector<4xi64>
    %145 = "llvm.shl"(%99, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %146 = "llvm.bitcast"(%145) : (vector<8xi32>) -> vector<4xi64>
    %147 = "llvm.mul"(%115, %80) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %148 = "llvm.mul"(%111, %133) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %149 = "llvm.mul"(%110, %85) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %150 = "llvm.mul"(%106, %137) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %151 = "llvm.mul"(%105, %90) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %152 = "llvm.mul"(%134, %141) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %153 = "llvm.mul"(%135, %95) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %154 = "llvm.mul"(%138, %144) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %155 = "llvm.mul"(%139, %100) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %156 = "llvm.mul"(%142, %146) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %157 = "llvm.add"(%151, %150) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %158 = "llvm.add"(%157, %149) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %159 = "llvm.add"(%158, %148) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %160 = "llvm.add"(%159, %147) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %161 = "llvm.add"(%160, %156) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %162 = "llvm.add"(%161, %155) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %163 = "llvm.add"(%162, %154) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %164 = "llvm.add"(%163, %153) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %165 = "llvm.add"(%164, %152) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %166 = "llvm.mul"(%116, %80) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %167 = "llvm.mul"(%115, %81) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %168 = "llvm.mul"(%111, %85) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %169 = "llvm.mul"(%110, %86) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %170 = "llvm.mul"(%106, %90) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %171 = "llvm.mul"(%105, %91) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %172 = "llvm.mul"(%134, %95) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %173 = "llvm.mul"(%135, %96) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %174 = "llvm.mul"(%138, %100) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %175 = "llvm.mul"(%139, %101) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %176 = "llvm.mul"(%120, %80) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %177 = "llvm.mul"(%116, %133) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %178 = "llvm.mul"(%115, %85) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %179 = "llvm.mul"(%111, %137) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %180 = "llvm.mul"(%110, %90) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %181 = "llvm.mul"(%106, %141) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %182 = "llvm.mul"(%105, %95) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %183 = "llvm.mul"(%134, %144) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %184 = "llvm.mul"(%135, %100) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %185 = "llvm.mul"(%138, %146) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %186 = "llvm.mul"(%121, %80) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %187 = "llvm.mul"(%120, %81) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %188 = "llvm.mul"(%116, %85) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %189 = "llvm.mul"(%115, %86) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %190 = "llvm.mul"(%111, %90) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %191 = "llvm.mul"(%110, %91) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %192 = "llvm.mul"(%106, %95) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %193 = "llvm.mul"(%105, %96) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %194 = "llvm.mul"(%134, %100) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %195 = "llvm.mul"(%135, %101) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %196 = "llvm.lshr"(%165, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %197 = "llvm.add"(%171, %170) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %198 = "llvm.add"(%197, %168) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %199 = "llvm.add"(%198, %169) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %200 = "llvm.add"(%199, %166) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %201 = "llvm.add"(%200, %167) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %202 = "llvm.add"(%201, %174) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %203 = "llvm.add"(%202, %175) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %204 = "llvm.add"(%203, %172) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %205 = "llvm.add"(%204, %173) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %206 = "llvm.add"(%205, %196) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %207 = "llvm.lshr"(%206, %40) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %208 = "llvm.add"(%182, %181) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %209 = "llvm.add"(%208, %179) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %210 = "llvm.add"(%209, %180) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %211 = "llvm.add"(%210, %178) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %212 = "llvm.add"(%211, %177) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %213 = "llvm.add"(%212, %176) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %214 = "llvm.add"(%213, %185) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %215 = "llvm.add"(%214, %184) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %216 = "llvm.add"(%215, %183) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %217 = "llvm.add"(%216, %207) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %218 = "llvm.lshr"(%217, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %219 = "llvm.add"(%193, %192) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %220 = "llvm.add"(%219, %190) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %221 = "llvm.add"(%220, %191) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %222 = "llvm.add"(%221, %188) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %223 = "llvm.add"(%222, %189) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %224 = "llvm.add"(%223, %186) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %225 = "llvm.add"(%224, %187) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %226 = "llvm.add"(%225, %194) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %227 = "llvm.add"(%226, %195) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %228 = "llvm.add"(%227, %218) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %229 = "llvm.bitcast"(%217) : (vector<4xi64>) -> vector<8xi32>
    %230 = "llvm.and"(%229, %58) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %231 = "llvm.bitcast"(%228) : (vector<4xi64>) -> vector<8xi32>
    %232 = "llvm.and"(%231, %76) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %233 = "llvm.shufflevector"(%230, %232) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %234 = "llvm.bitcast"(%233) : (vector<8xi32>) -> vector<4xi64>
    "llvm.return"(%234) : (vector<4xi64>) -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

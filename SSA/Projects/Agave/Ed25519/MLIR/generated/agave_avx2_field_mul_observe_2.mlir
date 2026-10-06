"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<vector<4xi64> (vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], sym_name = "agave_avx2_field_mul_observe_2", target_cpu = "x86-64", target_features = #llvm.target_features<["+avx", "+avx2", "+sse", "+sse2", "+sse3", "+sse4.1", "+sse4.2", "+crc32", "+ssse3"]>, unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
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
    %40 = "llvm.mlir.constant"() <{value = dense<67108863> : vector<4xi64>}> : () -> vector<4xi64>
    %41 = "llvm.mlir.constant"() <{value = dense<25> : vector<4xi64>}> : () -> vector<4xi64>
    %42 = "llvm.mlir.constant"() <{value = dense<33554431> : vector<4xi64>}> : () -> vector<4xi64>
    %43 = "llvm.mlir.constant"() <{value = 67108863 : i32}> : () -> i32
    %44 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %45 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %46 = "llvm.insertelement"(%44, %43, %45) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %47 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %48 = "llvm.insertelement"(%46, %0, %47) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %49 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %50 = "llvm.insertelement"(%48, %43, %49) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %51 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %52 = "llvm.insertelement"(%50, %0, %51) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %53 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %54 = "llvm.insertelement"(%52, %43, %53) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %55 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %56 = "llvm.insertelement"(%54, %0, %55) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %57 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %58 = "llvm.insertelement"(%56, %43, %57) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %59 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %60 = "llvm.insertelement"(%58, %0, %59) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %61 = "llvm.bitcast"(%arg0) : (vector<4xi64>) -> vector<8xi32>
    %62 = "llvm.shufflevector"(%61, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %63 = "llvm.shufflevector"(%61, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %64 = "llvm.bitcast"(%62) : (vector<8xi32>) -> vector<4xi64>
    %65 = "llvm.bitcast"(%63) : (vector<8xi32>) -> vector<4xi64>
    %66 = "llvm.bitcast"(%arg1) : (vector<4xi64>) -> vector<8xi32>
    %67 = "llvm.shufflevector"(%66, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %68 = "llvm.shufflevector"(%66, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %69 = "llvm.bitcast"(%67) : (vector<8xi32>) -> vector<4xi64>
    %70 = "llvm.bitcast"(%68) : (vector<8xi32>) -> vector<4xi64>
    %71 = "llvm.bitcast"(%arg2) : (vector<4xi64>) -> vector<8xi32>
    %72 = "llvm.shufflevector"(%71, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %73 = "llvm.shufflevector"(%71, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %74 = "llvm.bitcast"(%72) : (vector<8xi32>) -> vector<4xi64>
    %75 = "llvm.bitcast"(%73) : (vector<8xi32>) -> vector<4xi64>
    %76 = "llvm.bitcast"(%arg3) : (vector<4xi64>) -> vector<8xi32>
    %77 = "llvm.shufflevector"(%76, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %78 = "llvm.shufflevector"(%76, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %79 = "llvm.bitcast"(%77) : (vector<8xi32>) -> vector<4xi64>
    %80 = "llvm.bitcast"(%78) : (vector<8xi32>) -> vector<4xi64>
    %81 = "llvm.bitcast"(%arg4) : (vector<4xi64>) -> vector<8xi32>
    %82 = "llvm.shufflevector"(%81, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %83 = "llvm.shufflevector"(%81, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %84 = "llvm.bitcast"(%82) : (vector<8xi32>) -> vector<4xi64>
    %85 = "llvm.bitcast"(%83) : (vector<8xi32>) -> vector<4xi64>
    %86 = "llvm.bitcast"(%arg5) : (vector<4xi64>) -> vector<8xi32>
    %87 = "llvm.shufflevector"(%86, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %88 = "llvm.shufflevector"(%86, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %89 = "llvm.bitcast"(%87) : (vector<8xi32>) -> vector<4xi64>
    %90 = "llvm.bitcast"(%88) : (vector<8xi32>) -> vector<4xi64>
    %91 = "llvm.bitcast"(%arg6) : (vector<4xi64>) -> vector<8xi32>
    %92 = "llvm.shufflevector"(%91, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %93 = "llvm.shufflevector"(%91, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %94 = "llvm.bitcast"(%92) : (vector<8xi32>) -> vector<4xi64>
    %95 = "llvm.bitcast"(%93) : (vector<8xi32>) -> vector<4xi64>
    %96 = "llvm.bitcast"(%arg7) : (vector<4xi64>) -> vector<8xi32>
    %97 = "llvm.shufflevector"(%96, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %98 = "llvm.shufflevector"(%96, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %99 = "llvm.bitcast"(%97) : (vector<8xi32>) -> vector<4xi64>
    %100 = "llvm.bitcast"(%98) : (vector<8xi32>) -> vector<4xi64>
    %101 = "llvm.bitcast"(%arg8) : (vector<4xi64>) -> vector<8xi32>
    %102 = "llvm.shufflevector"(%101, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %103 = "llvm.shufflevector"(%101, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %104 = "llvm.bitcast"(%102) : (vector<8xi32>) -> vector<4xi64>
    %105 = "llvm.bitcast"(%103) : (vector<8xi32>) -> vector<4xi64>
    %106 = "llvm.bitcast"(%arg9) : (vector<4xi64>) -> vector<8xi32>
    %107 = "llvm.shufflevector"(%106, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %108 = "llvm.shufflevector"(%106, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %109 = "llvm.bitcast"(%107) : (vector<8xi32>) -> vector<4xi64>
    %110 = "llvm.bitcast"(%108) : (vector<8xi32>) -> vector<4xi64>
    %111 = "llvm.mul"(%90, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %112 = "llvm.mul"(%94, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %113 = "llvm.mul"(%95, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %114 = "llvm.mul"(%99, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %115 = "llvm.mul"(%100, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %116 = "llvm.mul"(%104, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %117 = "llvm.mul"(%105, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %118 = "llvm.mul"(%109, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %119 = "llvm.mul"(%110, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %120 = "llvm.mul"(%89, %64) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %121 = "llvm.shl"(%63, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %122 = "llvm.bitcast"(%121) : (vector<8xi32>) -> vector<4xi64>
    %123 = "llvm.and"(%119, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %124 = "llvm.mul"(%123, %122) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %125 = "llvm.and"(%118, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %126 = "llvm.mul"(%125, %69) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %127 = "llvm.shl"(%68, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %128 = "llvm.bitcast"(%127) : (vector<8xi32>) -> vector<4xi64>
    %129 = "llvm.and"(%117, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %130 = "llvm.mul"(%129, %128) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %131 = "llvm.and"(%116, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %132 = "llvm.mul"(%131, %74) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %133 = "llvm.shl"(%73, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %134 = "llvm.bitcast"(%133) : (vector<8xi32>) -> vector<4xi64>
    %135 = "llvm.and"(%115, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %136 = "llvm.mul"(%135, %134) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %137 = "llvm.and"(%114, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %138 = "llvm.mul"(%137, %79) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %139 = "llvm.shl"(%78, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %140 = "llvm.bitcast"(%139) : (vector<8xi32>) -> vector<4xi64>
    %141 = "llvm.and"(%113, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %142 = "llvm.mul"(%141, %140) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %143 = "llvm.and"(%112, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %144 = "llvm.mul"(%143, %84) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %145 = "llvm.shl"(%83, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %146 = "llvm.bitcast"(%145) : (vector<8xi32>) -> vector<4xi64>
    %147 = "llvm.and"(%111, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %148 = "llvm.mul"(%147, %146) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %149 = "llvm.add"(%148, %120) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %150 = "llvm.add"(%149, %144) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %151 = "llvm.add"(%150, %142) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %152 = "llvm.add"(%151, %138) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %153 = "llvm.add"(%152, %136) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %154 = "llvm.add"(%153, %132) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %155 = "llvm.add"(%154, %130) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %156 = "llvm.add"(%155, %126) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %157 = "llvm.add"(%156, %124) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %158 = "llvm.mul"(%90, %64) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %159 = "llvm.mul"(%89, %65) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %160 = "llvm.mul"(%123, %69) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %161 = "llvm.mul"(%125, %70) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %162 = "llvm.mul"(%129, %74) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %163 = "llvm.mul"(%131, %75) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %164 = "llvm.mul"(%135, %79) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %165 = "llvm.mul"(%137, %80) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %166 = "llvm.mul"(%141, %84) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %167 = "llvm.mul"(%143, %85) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %168 = "llvm.mul"(%94, %64) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %169 = "llvm.mul"(%90, %122) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %170 = "llvm.mul"(%89, %69) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %171 = "llvm.mul"(%123, %128) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %172 = "llvm.mul"(%125, %74) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %173 = "llvm.mul"(%129, %134) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %174 = "llvm.mul"(%131, %79) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %175 = "llvm.mul"(%135, %140) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %176 = "llvm.mul"(%137, %84) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %177 = "llvm.mul"(%141, %146) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %178 = "llvm.mul"(%95, %64) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %179 = "llvm.mul"(%94, %65) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %180 = "llvm.mul"(%90, %69) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %181 = "llvm.mul"(%89, %70) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %182 = "llvm.mul"(%123, %74) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %183 = "llvm.mul"(%125, %75) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %184 = "llvm.mul"(%129, %79) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %185 = "llvm.mul"(%131, %80) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %186 = "llvm.mul"(%135, %84) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %187 = "llvm.mul"(%137, %85) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %188 = "llvm.mul"(%99, %64) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %189 = "llvm.mul"(%95, %122) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %190 = "llvm.mul"(%94, %69) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %191 = "llvm.mul"(%90, %128) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %192 = "llvm.mul"(%89, %74) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %193 = "llvm.mul"(%123, %134) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %194 = "llvm.mul"(%125, %79) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %195 = "llvm.mul"(%129, %140) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %196 = "llvm.mul"(%131, %84) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %197 = "llvm.mul"(%135, %146) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %198 = "llvm.add"(%192, %191) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %199 = "llvm.add"(%198, %190) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %200 = "llvm.add"(%199, %189) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %201 = "llvm.add"(%200, %188) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %202 = "llvm.add"(%201, %197) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %203 = "llvm.add"(%202, %196) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %204 = "llvm.add"(%203, %195) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %205 = "llvm.add"(%204, %194) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %206 = "llvm.add"(%205, %193) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %207 = "llvm.mul"(%100, %64) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %208 = "llvm.mul"(%99, %65) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %209 = "llvm.mul"(%95, %69) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %210 = "llvm.mul"(%94, %70) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %211 = "llvm.mul"(%90, %74) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %212 = "llvm.mul"(%89, %75) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %213 = "llvm.mul"(%119, %79) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %214 = "llvm.mul"(%118, %80) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %215 = "llvm.mul"(%129, %84) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %216 = "llvm.mul"(%131, %85) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %217 = "llvm.lshr"(%157, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %218 = "llvm.add"(%159, %158) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %219 = "llvm.add"(%218, %166) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %220 = "llvm.add"(%219, %167) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %221 = "llvm.add"(%220, %164) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %222 = "llvm.add"(%221, %165) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %223 = "llvm.add"(%222, %162) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %224 = "llvm.add"(%223, %163) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %225 = "llvm.add"(%224, %160) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %226 = "llvm.add"(%225, %161) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %227 = "llvm.add"(%226, %217) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %228 = "llvm.lshr"(%206, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %229 = "llvm.add"(%212, %211) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %230 = "llvm.add"(%229, %209) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %231 = "llvm.add"(%230, %210) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %232 = "llvm.add"(%231, %207) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %233 = "llvm.add"(%232, %208) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %234 = "llvm.add"(%233, %215) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %235 = "llvm.add"(%234, %216) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %236 = "llvm.add"(%235, %213) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %237 = "llvm.add"(%236, %214) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %238 = "llvm.add"(%237, %228) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %239 = "llvm.and"(%206, %40) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %240 = "llvm.lshr"(%227, %41) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %241 = "llvm.add"(%170, %169) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %242 = "llvm.add"(%241, %168) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %243 = "llvm.add"(%242, %177) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %244 = "llvm.add"(%243, %176) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %245 = "llvm.add"(%244, %175) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %246 = "llvm.add"(%245, %174) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %247 = "llvm.add"(%246, %173) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %248 = "llvm.add"(%247, %172) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %249 = "llvm.add"(%248, %171) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %250 = "llvm.add"(%249, %240) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %251 = "llvm.and"(%238, %42) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %252 = "llvm.lshr"(%250, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %253 = "llvm.add"(%181, %180) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %254 = "llvm.add"(%253, %178) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %255 = "llvm.add"(%254, %179) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %256 = "llvm.add"(%255, %186) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %257 = "llvm.add"(%256, %187) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %258 = "llvm.add"(%257, %184) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %259 = "llvm.add"(%258, %185) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %260 = "llvm.add"(%259, %182) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %261 = "llvm.add"(%260, %183) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %262 = "llvm.add"(%261, %252) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %263 = "llvm.lshr"(%262, %41) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %264 = "llvm.add"(%263, %239) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %265 = "llvm.lshr"(%264, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %266 = "llvm.add"(%265, %251) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %267 = "llvm.bitcast"(%266) : (vector<4xi64>) -> vector<8xi32>
    %268 = "llvm.bitcast"(%264) : (vector<4xi64>) -> vector<8xi32>
    %269 = "llvm.and"(%268, %60) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %270 = "llvm.shufflevector"(%269, %267) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %271 = "llvm.bitcast"(%270) : (vector<8xi32>) -> vector<4xi64>
    "llvm.return"(%271) : (vector<4xi64>) -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

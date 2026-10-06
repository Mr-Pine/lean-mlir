"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<vector<4xi64> (vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], sym_name = "agave_avx2_field_square_negate_d_observe_1", target_cpu = "x86-64", target_features = #llvm.target_features<["+avx", "+avx2", "+sse", "+sse2", "+sse3", "+sse4.1", "+sse4.2", "+crc32", "+ssse3"]>, unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
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
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

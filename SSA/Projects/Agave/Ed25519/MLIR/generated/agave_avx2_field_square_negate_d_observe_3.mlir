"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<vector<4xi64> (vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], sym_name = "agave_avx2_field_square_negate_d_observe_3", target_cpu = "x86-64", target_features = #llvm.target_features<["+avx", "+avx2", "+sse", "+sse2", "+sse3", "+sse4.1", "+sse4.2", "+crc32", "+ssse3"]>, unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
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
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

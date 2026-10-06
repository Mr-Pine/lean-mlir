"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<vector<4xi64> (vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], sym_name = "agave_avx2_field_mul_observe_0", target_cpu = "x86-64", target_features = #llvm.target_features<["+avx", "+avx2", "+sse", "+sse2", "+sse3", "+sse4.1", "+sse4.2", "+crc32", "+ssse3"]>, unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
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
    %41 = "llvm.mlir.constant"() <{value = dense<33554431> : vector<4xi64>}> : () -> vector<4xi64>
    %42 = "llvm.mlir.constant"() <{value = dense<25> : vector<4xi64>}> : () -> vector<4xi64>
    %43 = "llvm.mlir.constant"() <{value = dense<51> : vector<4xi64>}> : () -> vector<4xi64>
    %44 = "llvm.mlir.constant"() <{value = 67108863 : i32}> : () -> i32
    %45 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %46 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %47 = "llvm.insertelement"(%45, %44, %46) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %48 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %49 = "llvm.insertelement"(%47, %0, %48) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %50 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %51 = "llvm.insertelement"(%49, %44, %50) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %52 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %53 = "llvm.insertelement"(%51, %0, %52) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %54 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %55 = "llvm.insertelement"(%53, %44, %54) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %56 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %57 = "llvm.insertelement"(%55, %0, %56) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %58 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %59 = "llvm.insertelement"(%57, %44, %58) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %60 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %61 = "llvm.insertelement"(%59, %0, %60) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %62 = "llvm.bitcast"(%arg0) : (vector<4xi64>) -> vector<8xi32>
    %63 = "llvm.shufflevector"(%62, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %64 = "llvm.shufflevector"(%62, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %65 = "llvm.bitcast"(%63) : (vector<8xi32>) -> vector<4xi64>
    %66 = "llvm.bitcast"(%64) : (vector<8xi32>) -> vector<4xi64>
    %67 = "llvm.bitcast"(%arg1) : (vector<4xi64>) -> vector<8xi32>
    %68 = "llvm.shufflevector"(%67, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %69 = "llvm.shufflevector"(%67, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %70 = "llvm.bitcast"(%68) : (vector<8xi32>) -> vector<4xi64>
    %71 = "llvm.bitcast"(%69) : (vector<8xi32>) -> vector<4xi64>
    %72 = "llvm.bitcast"(%arg2) : (vector<4xi64>) -> vector<8xi32>
    %73 = "llvm.shufflevector"(%72, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %74 = "llvm.shufflevector"(%72, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %75 = "llvm.bitcast"(%73) : (vector<8xi32>) -> vector<4xi64>
    %76 = "llvm.bitcast"(%74) : (vector<8xi32>) -> vector<4xi64>
    %77 = "llvm.bitcast"(%arg3) : (vector<4xi64>) -> vector<8xi32>
    %78 = "llvm.shufflevector"(%77, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %79 = "llvm.shufflevector"(%77, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %80 = "llvm.bitcast"(%78) : (vector<8xi32>) -> vector<4xi64>
    %81 = "llvm.bitcast"(%79) : (vector<8xi32>) -> vector<4xi64>
    %82 = "llvm.bitcast"(%arg4) : (vector<4xi64>) -> vector<8xi32>
    %83 = "llvm.shufflevector"(%82, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %84 = "llvm.shufflevector"(%82, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %85 = "llvm.bitcast"(%83) : (vector<8xi32>) -> vector<4xi64>
    %86 = "llvm.bitcast"(%84) : (vector<8xi32>) -> vector<4xi64>
    %87 = "llvm.bitcast"(%arg5) : (vector<4xi64>) -> vector<8xi32>
    %88 = "llvm.shufflevector"(%87, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %89 = "llvm.shufflevector"(%87, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %90 = "llvm.bitcast"(%88) : (vector<8xi32>) -> vector<4xi64>
    %91 = "llvm.bitcast"(%89) : (vector<8xi32>) -> vector<4xi64>
    %92 = "llvm.bitcast"(%arg6) : (vector<4xi64>) -> vector<8xi32>
    %93 = "llvm.shufflevector"(%92, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %94 = "llvm.shufflevector"(%92, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %95 = "llvm.bitcast"(%93) : (vector<8xi32>) -> vector<4xi64>
    %96 = "llvm.bitcast"(%94) : (vector<8xi32>) -> vector<4xi64>
    %97 = "llvm.bitcast"(%arg7) : (vector<4xi64>) -> vector<8xi32>
    %98 = "llvm.shufflevector"(%97, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %99 = "llvm.shufflevector"(%97, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %100 = "llvm.bitcast"(%98) : (vector<8xi32>) -> vector<4xi64>
    %101 = "llvm.bitcast"(%99) : (vector<8xi32>) -> vector<4xi64>
    %102 = "llvm.bitcast"(%arg8) : (vector<4xi64>) -> vector<8xi32>
    %103 = "llvm.shufflevector"(%102, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %104 = "llvm.shufflevector"(%102, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %105 = "llvm.bitcast"(%103) : (vector<8xi32>) -> vector<4xi64>
    %106 = "llvm.bitcast"(%104) : (vector<8xi32>) -> vector<4xi64>
    %107 = "llvm.bitcast"(%arg9) : (vector<4xi64>) -> vector<8xi32>
    %108 = "llvm.shufflevector"(%107, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %109 = "llvm.shufflevector"(%107, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %110 = "llvm.bitcast"(%108) : (vector<8xi32>) -> vector<4xi64>
    %111 = "llvm.bitcast"(%109) : (vector<8xi32>) -> vector<4xi64>
    %112 = "llvm.mul"(%91, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %113 = "llvm.mul"(%95, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %114 = "llvm.mul"(%96, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %115 = "llvm.mul"(%100, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %116 = "llvm.mul"(%101, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %117 = "llvm.mul"(%105, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %118 = "llvm.mul"(%106, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %119 = "llvm.mul"(%110, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %120 = "llvm.mul"(%111, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %121 = "llvm.mul"(%90, %65) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %122 = "llvm.shl"(%64, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %123 = "llvm.bitcast"(%122) : (vector<8xi32>) -> vector<4xi64>
    %124 = "llvm.and"(%120, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %125 = "llvm.mul"(%124, %123) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %126 = "llvm.and"(%119, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %127 = "llvm.mul"(%126, %70) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %128 = "llvm.shl"(%69, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %129 = "llvm.bitcast"(%128) : (vector<8xi32>) -> vector<4xi64>
    %130 = "llvm.and"(%118, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %131 = "llvm.mul"(%130, %129) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %132 = "llvm.and"(%117, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %133 = "llvm.mul"(%132, %75) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %134 = "llvm.shl"(%74, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %135 = "llvm.bitcast"(%134) : (vector<8xi32>) -> vector<4xi64>
    %136 = "llvm.and"(%116, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %137 = "llvm.mul"(%136, %135) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %138 = "llvm.and"(%115, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %139 = "llvm.mul"(%138, %80) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %140 = "llvm.shl"(%79, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %141 = "llvm.bitcast"(%140) : (vector<8xi32>) -> vector<4xi64>
    %142 = "llvm.and"(%114, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %143 = "llvm.mul"(%142, %141) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %144 = "llvm.and"(%113, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %145 = "llvm.mul"(%144, %85) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %146 = "llvm.shl"(%84, %37) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %147 = "llvm.bitcast"(%146) : (vector<8xi32>) -> vector<4xi64>
    %148 = "llvm.and"(%112, %38) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %149 = "llvm.mul"(%148, %147) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %150 = "llvm.add"(%149, %121) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %151 = "llvm.add"(%150, %145) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %152 = "llvm.add"(%151, %143) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %153 = "llvm.add"(%152, %139) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %154 = "llvm.add"(%153, %137) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %155 = "llvm.add"(%154, %133) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %156 = "llvm.add"(%155, %131) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %157 = "llvm.add"(%156, %127) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %158 = "llvm.add"(%157, %125) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %159 = "llvm.mul"(%91, %65) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %160 = "llvm.mul"(%90, %66) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %161 = "llvm.mul"(%120, %70) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %162 = "llvm.mul"(%119, %71) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %163 = "llvm.mul"(%130, %75) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %164 = "llvm.mul"(%132, %76) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %165 = "llvm.mul"(%136, %80) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %166 = "llvm.mul"(%138, %81) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %167 = "llvm.mul"(%142, %85) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %168 = "llvm.mul"(%144, %86) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %169 = "llvm.mul"(%100, %65) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %170 = "llvm.mul"(%96, %123) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %171 = "llvm.mul"(%95, %70) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %172 = "llvm.mul"(%91, %129) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %173 = "llvm.mul"(%90, %75) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %174 = "llvm.mul"(%124, %135) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %175 = "llvm.mul"(%126, %80) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %176 = "llvm.mul"(%130, %141) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %177 = "llvm.mul"(%132, %85) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %178 = "llvm.mul"(%136, %147) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %179 = "llvm.add"(%173, %172) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %180 = "llvm.add"(%179, %171) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %181 = "llvm.add"(%180, %170) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %182 = "llvm.add"(%181, %169) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %183 = "llvm.add"(%182, %178) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %184 = "llvm.add"(%183, %177) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %185 = "llvm.add"(%184, %176) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %186 = "llvm.add"(%185, %175) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %187 = "llvm.add"(%186, %174) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %188 = "llvm.mul"(%101, %65) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %189 = "llvm.mul"(%100, %66) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %190 = "llvm.mul"(%96, %70) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %191 = "llvm.mul"(%95, %71) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %192 = "llvm.mul"(%91, %75) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %193 = "llvm.mul"(%90, %76) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %194 = "llvm.mul"(%124, %80) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %195 = "llvm.mul"(%126, %81) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %196 = "llvm.mul"(%130, %85) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %197 = "llvm.mul"(%132, %86) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %198 = "llvm.mul"(%105, %65) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %199 = "llvm.mul"(%101, %123) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %200 = "llvm.mul"(%100, %70) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %201 = "llvm.mul"(%96, %129) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %202 = "llvm.mul"(%95, %75) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %203 = "llvm.mul"(%91, %135) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %204 = "llvm.mul"(%90, %80) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %205 = "llvm.mul"(%124, %141) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %206 = "llvm.mul"(%126, %85) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %207 = "llvm.mul"(%130, %147) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %208 = "llvm.mul"(%106, %65) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %209 = "llvm.mul"(%105, %66) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %210 = "llvm.mul"(%101, %70) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %211 = "llvm.mul"(%100, %71) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %212 = "llvm.mul"(%96, %75) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %213 = "llvm.mul"(%95, %76) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %214 = "llvm.mul"(%91, %80) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %215 = "llvm.mul"(%90, %81) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %216 = "llvm.mul"(%124, %85) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %217 = "llvm.mul"(%126, %86) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %218 = "llvm.mul"(%110, %65) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %219 = "llvm.mul"(%106, %123) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %220 = "llvm.mul"(%105, %70) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %221 = "llvm.mul"(%101, %129) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %222 = "llvm.mul"(%100, %75) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %223 = "llvm.mul"(%96, %135) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %224 = "llvm.mul"(%95, %80) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %225 = "llvm.mul"(%91, %141) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %226 = "llvm.mul"(%90, %85) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %227 = "llvm.mul"(%124, %147) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %228 = "llvm.mul"(%111, %65) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %229 = "llvm.mul"(%110, %66) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %230 = "llvm.mul"(%106, %70) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %231 = "llvm.mul"(%105, %71) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %232 = "llvm.mul"(%101, %75) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %233 = "llvm.mul"(%100, %76) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %234 = "llvm.mul"(%96, %80) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %235 = "llvm.mul"(%95, %81) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %236 = "llvm.mul"(%91, %85) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %237 = "llvm.mul"(%90, %86) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %238 = "llvm.lshr"(%158, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %239 = "llvm.add"(%160, %159) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %240 = "llvm.add"(%239, %167) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %241 = "llvm.add"(%240, %168) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %242 = "llvm.add"(%241, %165) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %243 = "llvm.add"(%242, %166) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %244 = "llvm.add"(%243, %163) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %245 = "llvm.add"(%244, %164) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %246 = "llvm.add"(%245, %161) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %247 = "llvm.add"(%246, %162) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %248 = "llvm.add"(%247, %238) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %249 = "llvm.and"(%158, %40) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %250 = "llvm.lshr"(%187, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %251 = "llvm.add"(%193, %192) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %252 = "llvm.add"(%251, %190) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %253 = "llvm.add"(%252, %191) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %254 = "llvm.add"(%253, %188) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %255 = "llvm.add"(%254, %189) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %256 = "llvm.add"(%255, %196) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %257 = "llvm.add"(%256, %197) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %258 = "llvm.add"(%257, %194) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %259 = "llvm.add"(%258, %195) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %260 = "llvm.add"(%259, %250) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %261 = "llvm.and"(%248, %41) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %262 = "llvm.lshr"(%260, %42) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %263 = "llvm.add"(%204, %203) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %264 = "llvm.add"(%263, %201) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %265 = "llvm.add"(%264, %202) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %266 = "llvm.add"(%265, %200) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %267 = "llvm.add"(%266, %199) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %268 = "llvm.add"(%267, %198) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %269 = "llvm.add"(%268, %207) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %270 = "llvm.add"(%269, %206) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %271 = "llvm.add"(%270, %205) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %272 = "llvm.add"(%271, %262) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %273 = "llvm.lshr"(%272, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %274 = "llvm.add"(%215, %214) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %275 = "llvm.add"(%274, %212) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %276 = "llvm.add"(%275, %213) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %277 = "llvm.add"(%276, %210) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %278 = "llvm.add"(%277, %211) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %279 = "llvm.add"(%278, %208) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %280 = "llvm.add"(%279, %209) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %281 = "llvm.add"(%280, %216) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %282 = "llvm.add"(%281, %217) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %283 = "llvm.add"(%282, %273) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %284 = "llvm.lshr"(%283, %42) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %285 = "llvm.add"(%225, %226) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %286 = "llvm.add"(%285, %224) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %287 = "llvm.add"(%286, %223) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %288 = "llvm.add"(%287, %222) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %289 = "llvm.add"(%288, %221) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %290 = "llvm.add"(%289, %220) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %291 = "llvm.add"(%290, %219) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %292 = "llvm.add"(%291, %218) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %293 = "llvm.add"(%292, %227) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %294 = "llvm.add"(%293, %284) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %295 = "llvm.lshr"(%294, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %296 = "llvm.add"(%237, %236) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %297 = "llvm.add"(%296, %234) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %298 = "llvm.add"(%297, %235) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %299 = "llvm.add"(%298, %232) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %300 = "llvm.add"(%299, %233) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %301 = "llvm.add"(%300, %230) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %302 = "llvm.add"(%301, %231) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %303 = "llvm.add"(%302, %228) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %304 = "llvm.add"(%303, %229) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %305 = "llvm.add"(%304, %295) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %306 = "llvm.lshr"(%305, %42) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %307 = "llvm.and"(%306, %40) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %308 = "llvm.lshr"(%305, %43) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %309 = "llvm.mul"(%307, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %310 = "llvm.mul"(%308, %36) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %311 = "llvm.add"(%309, %249) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %312 = "llvm.add"(%310, %261) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %313 = "llvm.lshr"(%311, %39) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %314 = "llvm.add"(%312, %313) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %315 = "llvm.bitcast"(%311) : (vector<4xi64>) -> vector<8xi32>
    %316 = "llvm.and"(%315, %61) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %317 = "llvm.bitcast"(%314) : (vector<4xi64>) -> vector<8xi32>
    %318 = "llvm.shufflevector"(%316, %317) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %319 = "llvm.bitcast"(%318) : (vector<8xi32>) -> vector<4xi64>
    "llvm.return"(%319) : (vector<4xi64>) -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

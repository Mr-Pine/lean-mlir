"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<vector<4xi64> (vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], sym_name = "agave_avx2_point_cached_add_observe_0", target_cpu = "x86-64", target_features = #llvm.target_features<["+avx", "+avx2", "+sse", "+sse2", "+sse3", "+sse4.1", "+sse4.2", "+crc32", "+ssse3"]>, unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>, %arg5: vector<4xi64>, %arg6: vector<4xi64>, %arg7: vector<4xi64>, %arg8: vector<4xi64>, %arg9: vector<4xi64>):
    %0 = "llvm.mlir.poison"() : () -> vector<8xi32>
    %1 = "llvm.mlir.poison"() : () -> i32
    %2 = "llvm.mlir.constant"() <{value = 67108862 : i32}> : () -> i32
    %3 = "llvm.mlir.constant"() <{value = 134217690 : i32}> : () -> i32
    %4 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %5 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %6 = "llvm.insertelement"(%4, %3, %5) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %7 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %8 = "llvm.insertelement"(%6, %1, %7) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %9 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %10 = "llvm.insertelement"(%8, %2, %9) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %11 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %12 = "llvm.insertelement"(%10, %1, %11) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %13 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %14 = "llvm.insertelement"(%12, %1, %13) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %15 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %16 = "llvm.insertelement"(%14, %1, %15) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %17 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %18 = "llvm.insertelement"(%16, %1, %17) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %19 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %20 = "llvm.insertelement"(%18, %1, %19) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %21 = "llvm.mlir.constant"() <{value = 134217726 : i32}> : () -> i32
    %22 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %23 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %24 = "llvm.insertelement"(%22, %21, %23) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %25 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %26 = "llvm.insertelement"(%24, %1, %25) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %27 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %28 = "llvm.insertelement"(%26, %2, %27) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %29 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %30 = "llvm.insertelement"(%28, %1, %29) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %31 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %32 = "llvm.insertelement"(%30, %1, %31) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %33 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %34 = "llvm.insertelement"(%32, %1, %33) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %35 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %36 = "llvm.insertelement"(%34, %1, %35) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %37 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %38 = "llvm.insertelement"(%36, %1, %37) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %39 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %40 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %41 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %42 = "llvm.insertelement"(%40, %39, %41) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %43 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %44 = "llvm.insertelement"(%42, %39, %43) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %45 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %46 = "llvm.insertelement"(%44, %1, %45) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %47 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %48 = "llvm.insertelement"(%46, %1, %47) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %49 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %50 = "llvm.insertelement"(%48, %39, %49) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %51 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %52 = "llvm.insertelement"(%50, %39, %51) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %53 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %54 = "llvm.insertelement"(%52, %1, %53) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %55 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %56 = "llvm.insertelement"(%54, %1, %55) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %57 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %58 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %59 = "llvm.insertelement"(%57, %1, %58) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %60 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %61 = "llvm.insertelement"(%59, %1, %60) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %62 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %63 = "llvm.insertelement"(%61, %39, %62) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %64 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %65 = "llvm.insertelement"(%63, %39, %64) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %66 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %67 = "llvm.insertelement"(%65, %1, %66) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %68 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %69 = "llvm.insertelement"(%67, %1, %68) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %70 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %71 = "llvm.insertelement"(%69, %39, %70) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %72 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %73 = "llvm.insertelement"(%71, %39, %72) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %74 = "llvm.mlir.constant"() <{value = dense<19> : vector<4xi64>}> : () -> vector<4xi64>
    %75 = "llvm.mlir.constant"() <{value = dense<1> : vector<8xi32>}> : () -> vector<8xi32>
    %76 = "llvm.mlir.constant"() <{value = dense<4294967295> : vector<4xi64>}> : () -> vector<4xi64>
    %77 = "llvm.mlir.constant"() <{value = dense<26> : vector<4xi64>}> : () -> vector<4xi64>
    %78 = "llvm.mlir.constant"() <{value = dense<67108863> : vector<4xi64>}> : () -> vector<4xi64>
    %79 = "llvm.mlir.constant"() <{value = dense<25> : vector<4xi64>}> : () -> vector<4xi64>
    %80 = "llvm.mlir.constant"() <{value = dense<33554431> : vector<4xi64>}> : () -> vector<4xi64>
    %81 = "llvm.mlir.constant"() <{value = dense<51> : vector<4xi64>}> : () -> vector<4xi64>
    %82 = "llvm.mlir.constant"() <{value = 67108863 : i32}> : () -> i32
    %83 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %84 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %85 = "llvm.insertelement"(%83, %82, %84) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %86 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %87 = "llvm.insertelement"(%85, %1, %86) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %88 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %89 = "llvm.insertelement"(%87, %82, %88) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %90 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %91 = "llvm.insertelement"(%89, %1, %90) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %92 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %93 = "llvm.insertelement"(%91, %82, %92) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %94 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %95 = "llvm.insertelement"(%93, %1, %94) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %96 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %97 = "llvm.insertelement"(%95, %82, %96) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %98 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %99 = "llvm.insertelement"(%97, %1, %98) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %100 = "llvm.mlir.constant"() <{value = 33554431 : i32}> : () -> i32
    %101 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %102 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %103 = "llvm.insertelement"(%101, %100, %102) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %104 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %105 = "llvm.insertelement"(%103, %1, %104) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %106 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %107 = "llvm.insertelement"(%105, %100, %106) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %108 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %109 = "llvm.insertelement"(%107, %1, %108) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %110 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %111 = "llvm.insertelement"(%109, %100, %110) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %112 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %113 = "llvm.insertelement"(%111, %1, %112) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %114 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %115 = "llvm.insertelement"(%113, %100, %114) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %116 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %117 = "llvm.insertelement"(%115, %1, %116) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %118 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %119 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %120 = "llvm.insertelement"(%118, %3, %119) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %121 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %122 = "llvm.insertelement"(%120, %1, %121) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %123 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %124 = "llvm.insertelement"(%122, %2, %123) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %125 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %126 = "llvm.insertelement"(%124, %1, %125) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %127 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %128 = "llvm.insertelement"(%126, %3, %127) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %129 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %130 = "llvm.insertelement"(%128, %1, %129) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %131 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %132 = "llvm.insertelement"(%130, %2, %131) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %133 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %134 = "llvm.insertelement"(%132, %1, %133) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %135 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %136 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %137 = "llvm.insertelement"(%135, %21, %136) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %138 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %139 = "llvm.insertelement"(%137, %1, %138) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %140 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %141 = "llvm.insertelement"(%139, %2, %140) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %142 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %143 = "llvm.insertelement"(%141, %1, %142) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %144 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %145 = "llvm.insertelement"(%143, %21, %144) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %146 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %147 = "llvm.insertelement"(%145, %1, %146) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %148 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %149 = "llvm.insertelement"(%147, %2, %148) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %150 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %151 = "llvm.insertelement"(%149, %1, %150) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %152 = "llvm.bitcast"(%arg0) : (vector<4xi64>) -> vector<8xi32>
    %153 = "llvm.bitcast"(%arg1) : (vector<4xi64>) -> vector<8xi32>
    %154 = "llvm.bitcast"(%arg2) : (vector<4xi64>) -> vector<8xi32>
    %155 = "llvm.bitcast"(%arg3) : (vector<4xi64>) -> vector<8xi32>
    %156 = "llvm.shufflevector"(%152, %0) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %157 = "llvm.shufflevector"(%153, %0) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %158 = "llvm.shufflevector"(%154, %0) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %159 = "llvm.shufflevector"(%155, %0) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %160 = "llvm.bitcast"(%arg4) : (vector<4xi64>) -> vector<8xi32>
    %161 = "llvm.shufflevector"(%160, %0) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %162 = "llvm.sub"(%20, %152) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %163 = "llvm.sub"(%38, %153) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %164 = "llvm.sub"(%38, %154) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %165 = "llvm.sub"(%38, %155) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %166 = "llvm.sub"(%38, %160) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %167 = "llvm.shufflevector"(%162, %152) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %168 = "llvm.shufflevector"(%163, %153) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %169 = "llvm.shufflevector"(%164, %154) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %170 = "llvm.shufflevector"(%165, %155) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %171 = "llvm.shufflevector"(%166, %160) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %172 = "llvm.add"(%167, %156) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %173 = "llvm.add"(%168, %157) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %174 = "llvm.add"(%169, %158) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %175 = "llvm.add"(%170, %159) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %176 = "llvm.add"(%171, %161) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %177 = "llvm.shufflevector"(%172, %152) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %178 = "llvm.shufflevector"(%173, %153) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %179 = "llvm.shufflevector"(%174, %154) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %180 = "llvm.shufflevector"(%175, %155) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %181 = "llvm.shufflevector"(%176, %160) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %182 = "llvm.shufflevector"(%177, %56) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %183 = "llvm.shufflevector"(%177, %73) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %184 = "llvm.bitcast"(%182) : (vector<8xi32>) -> vector<4xi64>
    %185 = "llvm.bitcast"(%183) : (vector<8xi32>) -> vector<4xi64>
    %186 = "llvm.shufflevector"(%178, %56) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %187 = "llvm.shufflevector"(%178, %73) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %188 = "llvm.bitcast"(%186) : (vector<8xi32>) -> vector<4xi64>
    %189 = "llvm.bitcast"(%187) : (vector<8xi32>) -> vector<4xi64>
    %190 = "llvm.shufflevector"(%179, %56) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %191 = "llvm.shufflevector"(%179, %73) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %192 = "llvm.bitcast"(%190) : (vector<8xi32>) -> vector<4xi64>
    %193 = "llvm.bitcast"(%191) : (vector<8xi32>) -> vector<4xi64>
    %194 = "llvm.shufflevector"(%180, %56) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %195 = "llvm.shufflevector"(%180, %73) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %196 = "llvm.bitcast"(%194) : (vector<8xi32>) -> vector<4xi64>
    %197 = "llvm.bitcast"(%195) : (vector<8xi32>) -> vector<4xi64>
    %198 = "llvm.shufflevector"(%181, %56) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %199 = "llvm.shufflevector"(%181, %73) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %200 = "llvm.bitcast"(%198) : (vector<8xi32>) -> vector<4xi64>
    %201 = "llvm.bitcast"(%199) : (vector<8xi32>) -> vector<4xi64>
    %202 = "llvm.bitcast"(%arg5) : (vector<4xi64>) -> vector<8xi32>
    %203 = "llvm.shufflevector"(%202, %56) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %204 = "llvm.shufflevector"(%202, %73) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %205 = "llvm.bitcast"(%203) : (vector<8xi32>) -> vector<4xi64>
    %206 = "llvm.bitcast"(%204) : (vector<8xi32>) -> vector<4xi64>
    %207 = "llvm.bitcast"(%arg6) : (vector<4xi64>) -> vector<8xi32>
    %208 = "llvm.shufflevector"(%207, %56) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %209 = "llvm.shufflevector"(%207, %73) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %210 = "llvm.bitcast"(%208) : (vector<8xi32>) -> vector<4xi64>
    %211 = "llvm.bitcast"(%209) : (vector<8xi32>) -> vector<4xi64>
    %212 = "llvm.bitcast"(%arg7) : (vector<4xi64>) -> vector<8xi32>
    %213 = "llvm.shufflevector"(%212, %56) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %214 = "llvm.shufflevector"(%212, %73) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %215 = "llvm.bitcast"(%213) : (vector<8xi32>) -> vector<4xi64>
    %216 = "llvm.bitcast"(%214) : (vector<8xi32>) -> vector<4xi64>
    %217 = "llvm.bitcast"(%arg8) : (vector<4xi64>) -> vector<8xi32>
    %218 = "llvm.shufflevector"(%217, %56) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %219 = "llvm.shufflevector"(%217, %73) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %220 = "llvm.bitcast"(%218) : (vector<8xi32>) -> vector<4xi64>
    %221 = "llvm.bitcast"(%219) : (vector<8xi32>) -> vector<4xi64>
    %222 = "llvm.bitcast"(%arg9) : (vector<4xi64>) -> vector<8xi32>
    %223 = "llvm.shufflevector"(%222, %56) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %224 = "llvm.shufflevector"(%222, %73) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %225 = "llvm.bitcast"(%223) : (vector<8xi32>) -> vector<4xi64>
    %226 = "llvm.bitcast"(%224) : (vector<8xi32>) -> vector<4xi64>
    %227 = "llvm.mul"(%206, %74) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %228 = "llvm.mul"(%210, %74) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %229 = "llvm.mul"(%211, %74) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %230 = "llvm.mul"(%215, %74) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %231 = "llvm.mul"(%216, %74) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %232 = "llvm.mul"(%220, %74) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %233 = "llvm.mul"(%221, %74) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %234 = "llvm.mul"(%225, %74) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %235 = "llvm.mul"(%226, %74) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %236 = "llvm.mul"(%205, %184) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %237 = "llvm.shl"(%183, %75) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %238 = "llvm.bitcast"(%237) : (vector<8xi32>) -> vector<4xi64>
    %239 = "llvm.and"(%235, %76) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %240 = "llvm.mul"(%239, %238) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %241 = "llvm.and"(%234, %76) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %242 = "llvm.mul"(%241, %188) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %243 = "llvm.shl"(%187, %75) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %244 = "llvm.bitcast"(%243) : (vector<8xi32>) -> vector<4xi64>
    %245 = "llvm.and"(%233, %76) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %246 = "llvm.mul"(%245, %244) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %247 = "llvm.and"(%232, %76) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %248 = "llvm.mul"(%247, %192) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %249 = "llvm.shl"(%191, %75) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %250 = "llvm.bitcast"(%249) : (vector<8xi32>) -> vector<4xi64>
    %251 = "llvm.and"(%231, %76) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %252 = "llvm.mul"(%251, %250) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %253 = "llvm.and"(%230, %76) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %254 = "llvm.mul"(%253, %196) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %255 = "llvm.shl"(%195, %75) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %256 = "llvm.bitcast"(%255) : (vector<8xi32>) -> vector<4xi64>
    %257 = "llvm.and"(%229, %76) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %258 = "llvm.mul"(%257, %256) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %259 = "llvm.and"(%228, %76) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %260 = "llvm.mul"(%259, %200) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %261 = "llvm.shl"(%199, %75) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %262 = "llvm.bitcast"(%261) : (vector<8xi32>) -> vector<4xi64>
    %263 = "llvm.and"(%227, %76) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %264 = "llvm.mul"(%263, %262) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %265 = "llvm.add"(%264, %236) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %266 = "llvm.add"(%265, %260) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %267 = "llvm.add"(%266, %258) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %268 = "llvm.add"(%267, %254) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %269 = "llvm.add"(%268, %252) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %270 = "llvm.add"(%269, %248) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %271 = "llvm.add"(%270, %246) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %272 = "llvm.add"(%271, %242) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %273 = "llvm.add"(%272, %240) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %274 = "llvm.mul"(%206, %184) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %275 = "llvm.mul"(%205, %185) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %276 = "llvm.mul"(%239, %188) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %277 = "llvm.mul"(%241, %189) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %278 = "llvm.mul"(%245, %192) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %279 = "llvm.mul"(%247, %193) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %280 = "llvm.mul"(%251, %196) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %281 = "llvm.mul"(%253, %197) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %282 = "llvm.mul"(%257, %200) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %283 = "llvm.mul"(%259, %201) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %284 = "llvm.mul"(%210, %184) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %285 = "llvm.mul"(%206, %238) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %286 = "llvm.mul"(%205, %188) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %287 = "llvm.mul"(%239, %244) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %288 = "llvm.mul"(%241, %192) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %289 = "llvm.mul"(%245, %250) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %290 = "llvm.mul"(%247, %196) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %291 = "llvm.mul"(%251, %256) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %292 = "llvm.mul"(%253, %200) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %293 = "llvm.mul"(%257, %262) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %294 = "llvm.mul"(%211, %184) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %295 = "llvm.mul"(%210, %185) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %296 = "llvm.mul"(%206, %188) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %297 = "llvm.mul"(%205, %189) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %298 = "llvm.mul"(%239, %192) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %299 = "llvm.mul"(%241, %193) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %300 = "llvm.mul"(%245, %196) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %301 = "llvm.mul"(%247, %197) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %302 = "llvm.mul"(%251, %200) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %303 = "llvm.mul"(%253, %201) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %304 = "llvm.mul"(%215, %184) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %305 = "llvm.mul"(%211, %238) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %306 = "llvm.mul"(%210, %188) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %307 = "llvm.mul"(%206, %244) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %308 = "llvm.mul"(%205, %192) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %309 = "llvm.mul"(%239, %250) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %310 = "llvm.mul"(%241, %196) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %311 = "llvm.mul"(%245, %256) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %312 = "llvm.mul"(%247, %200) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %313 = "llvm.mul"(%251, %262) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %314 = "llvm.add"(%308, %307) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %315 = "llvm.add"(%314, %306) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %316 = "llvm.add"(%315, %305) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %317 = "llvm.add"(%316, %304) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %318 = "llvm.add"(%317, %313) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %319 = "llvm.add"(%318, %312) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %320 = "llvm.add"(%319, %311) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %321 = "llvm.add"(%320, %310) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %322 = "llvm.add"(%321, %309) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %323 = "llvm.mul"(%216, %184) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %324 = "llvm.mul"(%215, %185) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %325 = "llvm.mul"(%211, %188) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %326 = "llvm.mul"(%210, %189) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %327 = "llvm.mul"(%206, %192) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %328 = "llvm.mul"(%205, %193) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %329 = "llvm.mul"(%239, %196) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %330 = "llvm.mul"(%241, %197) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %331 = "llvm.mul"(%245, %200) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %332 = "llvm.mul"(%247, %201) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %333 = "llvm.mul"(%220, %184) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %334 = "llvm.mul"(%216, %238) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %335 = "llvm.mul"(%215, %188) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %336 = "llvm.mul"(%211, %244) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %337 = "llvm.mul"(%210, %192) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %338 = "llvm.mul"(%206, %250) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %339 = "llvm.mul"(%205, %196) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %340 = "llvm.mul"(%239, %256) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %341 = "llvm.mul"(%241, %200) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %342 = "llvm.mul"(%245, %262) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %343 = "llvm.mul"(%221, %184) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %344 = "llvm.mul"(%220, %185) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %345 = "llvm.mul"(%216, %188) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %346 = "llvm.mul"(%215, %189) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %347 = "llvm.mul"(%211, %192) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %348 = "llvm.mul"(%210, %193) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %349 = "llvm.mul"(%206, %196) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %350 = "llvm.mul"(%205, %197) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %351 = "llvm.mul"(%239, %200) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %352 = "llvm.mul"(%241, %201) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %353 = "llvm.mul"(%225, %184) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %354 = "llvm.mul"(%221, %238) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %355 = "llvm.mul"(%220, %188) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %356 = "llvm.mul"(%216, %244) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %357 = "llvm.mul"(%215, %192) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %358 = "llvm.mul"(%211, %250) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %359 = "llvm.mul"(%210, %196) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %360 = "llvm.mul"(%206, %256) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %361 = "llvm.mul"(%205, %200) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %362 = "llvm.mul"(%239, %262) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %363 = "llvm.mul"(%226, %184) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %364 = "llvm.mul"(%225, %185) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %365 = "llvm.mul"(%221, %188) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %366 = "llvm.mul"(%220, %189) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %367 = "llvm.mul"(%216, %192) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %368 = "llvm.mul"(%215, %193) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %369 = "llvm.mul"(%211, %196) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %370 = "llvm.mul"(%210, %197) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %371 = "llvm.mul"(%206, %200) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %372 = "llvm.mul"(%205, %201) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %373 = "llvm.lshr"(%273, %77) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %374 = "llvm.add"(%275, %274) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %375 = "llvm.add"(%374, %282) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %376 = "llvm.add"(%375, %283) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %377 = "llvm.add"(%376, %280) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %378 = "llvm.add"(%377, %281) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %379 = "llvm.add"(%378, %278) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %380 = "llvm.add"(%379, %279) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %381 = "llvm.add"(%380, %276) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %382 = "llvm.add"(%381, %277) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %383 = "llvm.add"(%382, %373) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %384 = "llvm.and"(%273, %78) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %385 = "llvm.lshr"(%322, %77) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %386 = "llvm.add"(%328, %327) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %387 = "llvm.add"(%386, %325) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %388 = "llvm.add"(%387, %326) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %389 = "llvm.add"(%388, %323) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %390 = "llvm.add"(%389, %324) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %391 = "llvm.add"(%390, %331) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %392 = "llvm.add"(%391, %332) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %393 = "llvm.add"(%392, %329) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %394 = "llvm.add"(%393, %330) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %395 = "llvm.add"(%394, %385) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %396 = "llvm.and"(%322, %78) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %397 = "llvm.lshr"(%383, %79) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %398 = "llvm.add"(%286, %285) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %399 = "llvm.add"(%398, %284) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %400 = "llvm.add"(%399, %293) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %401 = "llvm.add"(%400, %292) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %402 = "llvm.add"(%401, %291) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %403 = "llvm.add"(%402, %290) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %404 = "llvm.add"(%403, %289) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %405 = "llvm.add"(%404, %288) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %406 = "llvm.add"(%405, %287) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %407 = "llvm.add"(%406, %397) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %408 = "llvm.and"(%383, %80) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %409 = "llvm.lshr"(%395, %79) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %410 = "llvm.add"(%339, %338) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %411 = "llvm.add"(%410, %336) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %412 = "llvm.add"(%411, %337) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %413 = "llvm.add"(%412, %335) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %414 = "llvm.add"(%413, %334) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %415 = "llvm.add"(%414, %333) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %416 = "llvm.add"(%415, %342) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %417 = "llvm.add"(%416, %341) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %418 = "llvm.add"(%417, %340) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %419 = "llvm.add"(%418, %409) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %420 = "llvm.and"(%395, %80) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %421 = "llvm.lshr"(%407, %77) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %422 = "llvm.add"(%297, %296) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %423 = "llvm.add"(%422, %294) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %424 = "llvm.add"(%423, %295) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %425 = "llvm.add"(%424, %302) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %426 = "llvm.add"(%425, %303) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %427 = "llvm.add"(%426, %300) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %428 = "llvm.add"(%427, %301) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %429 = "llvm.add"(%428, %298) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %430 = "llvm.add"(%429, %299) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %431 = "llvm.add"(%430, %421) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %432 = "llvm.lshr"(%419, %77) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %433 = "llvm.add"(%350, %349) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %434 = "llvm.add"(%433, %347) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %435 = "llvm.add"(%434, %348) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %436 = "llvm.add"(%435, %345) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %437 = "llvm.add"(%436, %346) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %438 = "llvm.add"(%437, %343) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %439 = "llvm.add"(%438, %344) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %440 = "llvm.add"(%439, %351) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %441 = "llvm.add"(%440, %352) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %442 = "llvm.add"(%441, %432) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %443 = "llvm.lshr"(%431, %79) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %444 = "llvm.add"(%443, %396) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %445 = "llvm.lshr"(%442, %79) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %446 = "llvm.add"(%360, %361) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %447 = "llvm.add"(%446, %359) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %448 = "llvm.add"(%447, %358) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %449 = "llvm.add"(%448, %357) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %450 = "llvm.add"(%449, %356) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %451 = "llvm.add"(%450, %355) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %452 = "llvm.add"(%451, %354) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %453 = "llvm.add"(%452, %353) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %454 = "llvm.add"(%453, %362) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %455 = "llvm.add"(%454, %445) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %456 = "llvm.lshr"(%444, %77) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %457 = "llvm.add"(%456, %420) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %458 = "llvm.lshr"(%455, %77) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %459 = "llvm.add"(%372, %371) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %460 = "llvm.add"(%459, %369) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %461 = "llvm.add"(%460, %370) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %462 = "llvm.add"(%461, %367) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %463 = "llvm.add"(%462, %368) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %464 = "llvm.add"(%463, %365) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %465 = "llvm.add"(%464, %366) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %466 = "llvm.add"(%465, %363) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %467 = "llvm.add"(%466, %364) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %468 = "llvm.add"(%467, %458) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %469 = "llvm.lshr"(%468, %79) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %470 = "llvm.and"(%469, %78) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %471 = "llvm.lshr"(%468, %81) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %472 = "llvm.mul"(%470, %74) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %473 = "llvm.mul"(%471, %74) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %474 = "llvm.add"(%472, %384) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %475 = "llvm.add"(%473, %408) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %476 = "llvm.lshr"(%474, %77) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %477 = "llvm.add"(%475, %476) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %478 = "llvm.bitcast"(%474) : (vector<4xi64>) -> vector<8xi32>
    %479 = "llvm.and"(%478, %99) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %480 = "llvm.bitcast"(%477) : (vector<4xi64>) -> vector<8xi32>
    %481 = "llvm.shufflevector"(%479, %480) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %482 = "llvm.bitcast"(%407) : (vector<4xi64>) -> vector<8xi32>
    %483 = "llvm.and"(%482, %99) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %484 = "llvm.bitcast"(%431) : (vector<4xi64>) -> vector<8xi32>
    %485 = "llvm.and"(%484, %117) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %486 = "llvm.shufflevector"(%483, %485) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %487 = "llvm.bitcast"(%457) : (vector<4xi64>) -> vector<8xi32>
    %488 = "llvm.bitcast"(%444) : (vector<4xi64>) -> vector<8xi32>
    %489 = "llvm.and"(%488, %99) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %490 = "llvm.shufflevector"(%489, %487) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %491 = "llvm.bitcast"(%419) : (vector<4xi64>) -> vector<8xi32>
    %492 = "llvm.and"(%491, %99) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %493 = "llvm.bitcast"(%442) : (vector<4xi64>) -> vector<8xi32>
    %494 = "llvm.and"(%493, %117) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %495 = "llvm.shufflevector"(%492, %494) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %496 = "llvm.bitcast"(%455) : (vector<4xi64>) -> vector<8xi32>
    %497 = "llvm.and"(%496, %99) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %498 = "llvm.bitcast"(%468) : (vector<4xi64>) -> vector<8xi32>
    %499 = "llvm.and"(%498, %117) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %500 = "llvm.shufflevector"(%497, %499) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %501 = "llvm.shufflevector"(%481, %0) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %502 = "llvm.shufflevector"(%486, %0) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %503 = "llvm.shufflevector"(%490, %0) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %504 = "llvm.shufflevector"(%495, %0) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %505 = "llvm.shufflevector"(%500, %0) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %506 = "llvm.shufflevector"(%481, %0) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %507 = "llvm.shufflevector"(%486, %0) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %508 = "llvm.shufflevector"(%490, %0) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %509 = "llvm.shufflevector"(%495, %0) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %510 = "llvm.shufflevector"(%500, %0) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %511 = "llvm.sub"(%134, %501) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %512 = "llvm.sub"(%151, %502) <{overflowFlags = 1 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %513 = "llvm.sub"(%151, %503) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %514 = "llvm.sub"(%151, %504) <{overflowFlags = 1 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %515 = "llvm.sub"(%151, %505) <{overflowFlags = 1 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %516 = "llvm.shufflevector"(%511, %501) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %517 = "llvm.shufflevector"(%512, %502) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %518 = "llvm.shufflevector"(%513, %503) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %519 = "llvm.shufflevector"(%514, %504) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %520 = "llvm.shufflevector"(%515, %505) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %521 = "llvm.add"(%516, %506) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %522 = "llvm.add"(%517, %507) <{overflowFlags = 1 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %523 = "llvm.add"(%518, %508) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %524 = "llvm.add"(%519, %509) <{overflowFlags = 1 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %525 = "llvm.add"(%520, %510) <{overflowFlags = 1 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %526 = "llvm.shufflevector"(%521, %0) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %527 = "llvm.shufflevector"(%522, %0) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %528 = "llvm.shufflevector"(%523, %0) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %529 = "llvm.shufflevector"(%524, %0) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %530 = "llvm.shufflevector"(%525, %0) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %531 = "llvm.shufflevector"(%521, %0) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %532 = "llvm.shufflevector"(%522, %0) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %533 = "llvm.shufflevector"(%523, %0) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %534 = "llvm.shufflevector"(%524, %0) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %535 = "llvm.shufflevector"(%525, %0) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %536 = "llvm.shufflevector"(%526, %56) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %537 = "llvm.shufflevector"(%526, %73) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %538 = "llvm.bitcast"(%536) : (vector<8xi32>) -> vector<4xi64>
    %539 = "llvm.bitcast"(%537) : (vector<8xi32>) -> vector<4xi64>
    %540 = "llvm.shufflevector"(%527, %56) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %541 = "llvm.shufflevector"(%527, %73) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %542 = "llvm.bitcast"(%540) : (vector<8xi32>) -> vector<4xi64>
    %543 = "llvm.bitcast"(%541) : (vector<8xi32>) -> vector<4xi64>
    %544 = "llvm.shufflevector"(%528, %56) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %545 = "llvm.shufflevector"(%528, %73) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %546 = "llvm.bitcast"(%544) : (vector<8xi32>) -> vector<4xi64>
    %547 = "llvm.bitcast"(%545) : (vector<8xi32>) -> vector<4xi64>
    %548 = "llvm.shufflevector"(%529, %56) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %549 = "llvm.shufflevector"(%529, %73) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %550 = "llvm.bitcast"(%548) : (vector<8xi32>) -> vector<4xi64>
    %551 = "llvm.bitcast"(%549) : (vector<8xi32>) -> vector<4xi64>
    %552 = "llvm.shufflevector"(%530, %56) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %553 = "llvm.shufflevector"(%530, %73) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %554 = "llvm.bitcast"(%552) : (vector<8xi32>) -> vector<4xi64>
    %555 = "llvm.bitcast"(%553) : (vector<8xi32>) -> vector<4xi64>
    %556 = "llvm.shufflevector"(%531, %56) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %557 = "llvm.shufflevector"(%531, %73) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %558 = "llvm.bitcast"(%556) : (vector<8xi32>) -> vector<4xi64>
    %559 = "llvm.bitcast"(%557) : (vector<8xi32>) -> vector<4xi64>
    %560 = "llvm.shufflevector"(%532, %56) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %561 = "llvm.shufflevector"(%532, %73) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %562 = "llvm.bitcast"(%560) : (vector<8xi32>) -> vector<4xi64>
    %563 = "llvm.bitcast"(%561) : (vector<8xi32>) -> vector<4xi64>
    %564 = "llvm.shufflevector"(%533, %56) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %565 = "llvm.shufflevector"(%533, %73) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %566 = "llvm.bitcast"(%564) : (vector<8xi32>) -> vector<4xi64>
    %567 = "llvm.bitcast"(%565) : (vector<8xi32>) -> vector<4xi64>
    %568 = "llvm.shufflevector"(%534, %56) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %569 = "llvm.shufflevector"(%534, %73) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %570 = "llvm.bitcast"(%568) : (vector<8xi32>) -> vector<4xi64>
    %571 = "llvm.bitcast"(%569) : (vector<8xi32>) -> vector<4xi64>
    %572 = "llvm.shufflevector"(%535, %56) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %573 = "llvm.shufflevector"(%535, %73) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %574 = "llvm.bitcast"(%572) : (vector<8xi32>) -> vector<4xi64>
    %575 = "llvm.bitcast"(%573) : (vector<8xi32>) -> vector<4xi64>
    %576 = "llvm.mul"(%559, %74) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %577 = "llvm.mul"(%562, %74) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %578 = "llvm.mul"(%563, %74) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %579 = "llvm.mul"(%566, %74) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %580 = "llvm.mul"(%567, %74) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %581 = "llvm.mul"(%570, %74) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %582 = "llvm.mul"(%571, %74) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %583 = "llvm.mul"(%574, %74) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %584 = "llvm.mul"(%575, %74) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %585 = "llvm.mul"(%558, %538) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %586 = "llvm.shl"(%537, %75) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %587 = "llvm.bitcast"(%586) : (vector<8xi32>) -> vector<4xi64>
    %588 = "llvm.and"(%584, %76) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %589 = "llvm.mul"(%588, %587) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %590 = "llvm.and"(%583, %76) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %591 = "llvm.mul"(%590, %542) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %592 = "llvm.shl"(%541, %75) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %593 = "llvm.bitcast"(%592) : (vector<8xi32>) -> vector<4xi64>
    %594 = "llvm.and"(%582, %76) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %595 = "llvm.mul"(%594, %593) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %596 = "llvm.and"(%581, %76) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %597 = "llvm.mul"(%596, %546) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %598 = "llvm.shl"(%545, %75) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %599 = "llvm.bitcast"(%598) : (vector<8xi32>) -> vector<4xi64>
    %600 = "llvm.and"(%580, %76) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %601 = "llvm.mul"(%600, %599) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %602 = "llvm.and"(%579, %76) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %603 = "llvm.mul"(%602, %550) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %604 = "llvm.shl"(%549, %75) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %605 = "llvm.bitcast"(%604) : (vector<8xi32>) -> vector<4xi64>
    %606 = "llvm.and"(%578, %76) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %607 = "llvm.mul"(%606, %605) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %608 = "llvm.and"(%577, %76) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %609 = "llvm.mul"(%608, %554) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %610 = "llvm.shl"(%553, %75) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %611 = "llvm.bitcast"(%610) : (vector<8xi32>) -> vector<4xi64>
    %612 = "llvm.and"(%576, %76) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %613 = "llvm.mul"(%612, %611) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %614 = "llvm.add"(%613, %585) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %615 = "llvm.add"(%614, %609) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %616 = "llvm.add"(%615, %607) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %617 = "llvm.add"(%616, %603) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %618 = "llvm.add"(%617, %601) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %619 = "llvm.add"(%618, %597) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %620 = "llvm.add"(%619, %595) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %621 = "llvm.add"(%620, %591) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %622 = "llvm.add"(%621, %589) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %623 = "llvm.mul"(%559, %538) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %624 = "llvm.mul"(%558, %539) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %625 = "llvm.mul"(%584, %542) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %626 = "llvm.mul"(%583, %543) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %627 = "llvm.mul"(%594, %546) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %628 = "llvm.mul"(%596, %547) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %629 = "llvm.mul"(%600, %550) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %630 = "llvm.mul"(%602, %551) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %631 = "llvm.mul"(%606, %554) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %632 = "llvm.mul"(%608, %555) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %633 = "llvm.mul"(%566, %538) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %634 = "llvm.mul"(%563, %587) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %635 = "llvm.mul"(%562, %542) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %636 = "llvm.mul"(%559, %593) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %637 = "llvm.mul"(%558, %546) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %638 = "llvm.mul"(%588, %599) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %639 = "llvm.mul"(%590, %550) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %640 = "llvm.mul"(%594, %605) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %641 = "llvm.mul"(%596, %554) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %642 = "llvm.mul"(%600, %611) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %643 = "llvm.add"(%637, %636) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %644 = "llvm.add"(%643, %635) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %645 = "llvm.add"(%644, %634) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %646 = "llvm.add"(%645, %633) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %647 = "llvm.add"(%646, %642) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %648 = "llvm.add"(%647, %641) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %649 = "llvm.add"(%648, %640) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %650 = "llvm.add"(%649, %639) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %651 = "llvm.add"(%650, %638) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %652 = "llvm.mul"(%567, %538) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %653 = "llvm.mul"(%566, %539) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %654 = "llvm.mul"(%563, %542) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %655 = "llvm.mul"(%562, %543) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %656 = "llvm.mul"(%559, %546) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %657 = "llvm.mul"(%558, %547) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %658 = "llvm.mul"(%588, %550) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %659 = "llvm.mul"(%590, %551) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %660 = "llvm.mul"(%594, %554) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %661 = "llvm.mul"(%596, %555) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %662 = "llvm.mul"(%570, %538) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %663 = "llvm.mul"(%567, %587) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %664 = "llvm.mul"(%566, %542) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %665 = "llvm.mul"(%563, %593) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %666 = "llvm.mul"(%562, %546) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %667 = "llvm.mul"(%559, %599) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %668 = "llvm.mul"(%558, %550) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %669 = "llvm.mul"(%588, %605) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %670 = "llvm.mul"(%590, %554) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %671 = "llvm.mul"(%594, %611) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %672 = "llvm.mul"(%571, %538) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %673 = "llvm.mul"(%570, %539) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %674 = "llvm.mul"(%567, %542) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %675 = "llvm.mul"(%566, %543) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %676 = "llvm.mul"(%563, %546) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %677 = "llvm.mul"(%562, %547) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %678 = "llvm.mul"(%559, %550) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %679 = "llvm.mul"(%558, %551) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %680 = "llvm.mul"(%588, %554) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %681 = "llvm.mul"(%590, %555) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %682 = "llvm.mul"(%574, %538) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %683 = "llvm.mul"(%571, %587) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %684 = "llvm.mul"(%570, %542) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %685 = "llvm.mul"(%567, %593) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %686 = "llvm.mul"(%566, %546) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %687 = "llvm.mul"(%563, %599) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %688 = "llvm.mul"(%562, %550) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %689 = "llvm.mul"(%559, %605) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %690 = "llvm.mul"(%558, %554) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %691 = "llvm.mul"(%588, %611) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %692 = "llvm.mul"(%575, %538) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %693 = "llvm.mul"(%574, %539) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %694 = "llvm.mul"(%571, %542) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %695 = "llvm.mul"(%570, %543) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %696 = "llvm.mul"(%567, %546) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %697 = "llvm.mul"(%566, %547) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %698 = "llvm.mul"(%563, %550) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %699 = "llvm.mul"(%562, %551) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %700 = "llvm.mul"(%559, %554) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %701 = "llvm.mul"(%558, %555) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %702 = "llvm.lshr"(%622, %77) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %703 = "llvm.add"(%624, %623) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %704 = "llvm.add"(%703, %631) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %705 = "llvm.add"(%704, %632) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %706 = "llvm.add"(%705, %629) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %707 = "llvm.add"(%706, %630) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %708 = "llvm.add"(%707, %627) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %709 = "llvm.add"(%708, %628) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %710 = "llvm.add"(%709, %625) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %711 = "llvm.add"(%710, %626) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %712 = "llvm.add"(%711, %702) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %713 = "llvm.and"(%622, %78) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %714 = "llvm.lshr"(%651, %77) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %715 = "llvm.add"(%657, %656) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %716 = "llvm.add"(%715, %654) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %717 = "llvm.add"(%716, %655) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %718 = "llvm.add"(%717, %652) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %719 = "llvm.add"(%718, %653) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %720 = "llvm.add"(%719, %660) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %721 = "llvm.add"(%720, %661) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %722 = "llvm.add"(%721, %658) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %723 = "llvm.add"(%722, %659) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %724 = "llvm.add"(%723, %714) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %725 = "llvm.and"(%712, %80) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %726 = "llvm.lshr"(%724, %79) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %727 = "llvm.add"(%668, %667) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %728 = "llvm.add"(%727, %665) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %729 = "llvm.add"(%728, %666) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %730 = "llvm.add"(%729, %664) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %731 = "llvm.add"(%730, %663) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %732 = "llvm.add"(%731, %662) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %733 = "llvm.add"(%732, %671) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %734 = "llvm.add"(%733, %670) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %735 = "llvm.add"(%734, %669) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %736 = "llvm.add"(%735, %726) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %737 = "llvm.lshr"(%736, %77) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %738 = "llvm.add"(%679, %678) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %739 = "llvm.add"(%738, %676) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %740 = "llvm.add"(%739, %677) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %741 = "llvm.add"(%740, %674) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %742 = "llvm.add"(%741, %675) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %743 = "llvm.add"(%742, %672) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %744 = "llvm.add"(%743, %673) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %745 = "llvm.add"(%744, %680) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %746 = "llvm.add"(%745, %681) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %747 = "llvm.add"(%746, %737) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %748 = "llvm.lshr"(%747, %79) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %749 = "llvm.add"(%689, %690) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %750 = "llvm.add"(%749, %688) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %751 = "llvm.add"(%750, %687) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %752 = "llvm.add"(%751, %686) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %753 = "llvm.add"(%752, %685) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %754 = "llvm.add"(%753, %684) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %755 = "llvm.add"(%754, %683) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %756 = "llvm.add"(%755, %682) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %757 = "llvm.add"(%756, %691) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %758 = "llvm.add"(%757, %748) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %759 = "llvm.lshr"(%758, %77) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %760 = "llvm.add"(%701, %700) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %761 = "llvm.add"(%760, %698) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %762 = "llvm.add"(%761, %699) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %763 = "llvm.add"(%762, %696) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %764 = "llvm.add"(%763, %697) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %765 = "llvm.add"(%764, %694) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %766 = "llvm.add"(%765, %695) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %767 = "llvm.add"(%766, %692) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %768 = "llvm.add"(%767, %693) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %769 = "llvm.add"(%768, %759) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %770 = "llvm.lshr"(%769, %79) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %771 = "llvm.and"(%770, %78) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %772 = "llvm.lshr"(%769, %81) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %773 = "llvm.mul"(%771, %74) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %774 = "llvm.mul"(%772, %74) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %775 = "llvm.add"(%773, %713) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %776 = "llvm.add"(%774, %725) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %777 = "llvm.lshr"(%775, %77) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %778 = "llvm.add"(%776, %777) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %779 = "llvm.bitcast"(%775) : (vector<4xi64>) -> vector<8xi32>
    %780 = "llvm.and"(%779, %99) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %781 = "llvm.bitcast"(%778) : (vector<4xi64>) -> vector<8xi32>
    %782 = "llvm.shufflevector"(%780, %781) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %783 = "llvm.bitcast"(%782) : (vector<8xi32>) -> vector<4xi64>
    "llvm.return"(%783) : (vector<4xi64>) -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<vector<4xi64> (vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], sym_name = "agave_avx2_point_cached_sub_observe_0", target_cpu = "x86-64", target_features = #llvm.target_features<["+avx", "+avx2", "+sse", "+sse2", "+sse3", "+sse4.1", "+sse4.2", "+crc32", "+ssse3"]>, unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>, %arg5: vector<4xi64>, %arg6: vector<4xi64>, %arg7: vector<4xi64>, %arg8: vector<4xi64>, %arg9: vector<4xi64>):
    %0 = "llvm.mlir.poison"() : () -> vector<8xi32>
    %1 = "llvm.mlir.constant"() <{value = 67108862 : i32}> : () -> i32
    %2 = "llvm.mlir.poison"() : () -> i32
    %3 = "llvm.mlir.constant"() <{value = 134217690 : i32}> : () -> i32
    %4 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %5 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %6 = "llvm.insertelement"(%4, %2, %5) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %7 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %8 = "llvm.insertelement"(%6, %2, %7) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %9 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %10 = "llvm.insertelement"(%8, %2, %9) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %11 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %12 = "llvm.insertelement"(%10, %2, %11) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %13 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %14 = "llvm.insertelement"(%12, %2, %13) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %15 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %16 = "llvm.insertelement"(%14, %3, %15) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %17 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %18 = "llvm.insertelement"(%16, %2, %17) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %19 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %20 = "llvm.insertelement"(%18, %1, %19) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %21 = "llvm.mlir.constant"() <{value = 134217726 : i32}> : () -> i32
    %22 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %23 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %24 = "llvm.insertelement"(%22, %2, %23) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %25 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %26 = "llvm.insertelement"(%24, %2, %25) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %27 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %28 = "llvm.insertelement"(%26, %2, %27) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %29 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %30 = "llvm.insertelement"(%28, %2, %29) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %31 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %32 = "llvm.insertelement"(%30, %2, %31) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %33 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %34 = "llvm.insertelement"(%32, %21, %33) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %35 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %36 = "llvm.insertelement"(%34, %2, %35) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %37 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %38 = "llvm.insertelement"(%36, %1, %37) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %39 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %40 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %41 = "llvm.insertelement"(%39, %3, %40) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %42 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %43 = "llvm.insertelement"(%41, %2, %42) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %44 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %45 = "llvm.insertelement"(%43, %1, %44) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %46 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %47 = "llvm.insertelement"(%45, %2, %46) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %48 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %49 = "llvm.insertelement"(%47, %2, %48) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %50 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %51 = "llvm.insertelement"(%49, %2, %50) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %52 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %53 = "llvm.insertelement"(%51, %2, %52) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %54 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %55 = "llvm.insertelement"(%53, %2, %54) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %56 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %57 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %58 = "llvm.insertelement"(%56, %21, %57) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %59 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %60 = "llvm.insertelement"(%58, %2, %59) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %61 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %62 = "llvm.insertelement"(%60, %1, %61) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %63 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %64 = "llvm.insertelement"(%62, %2, %63) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %65 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %66 = "llvm.insertelement"(%64, %2, %65) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %67 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %68 = "llvm.insertelement"(%66, %2, %67) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %69 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %70 = "llvm.insertelement"(%68, %2, %69) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %71 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %72 = "llvm.insertelement"(%70, %2, %71) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %73 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %74 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %75 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %76 = "llvm.insertelement"(%74, %73, %75) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %77 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %78 = "llvm.insertelement"(%76, %73, %77) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %79 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %80 = "llvm.insertelement"(%78, %2, %79) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %81 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %82 = "llvm.insertelement"(%80, %2, %81) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %83 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %84 = "llvm.insertelement"(%82, %73, %83) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %85 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %86 = "llvm.insertelement"(%84, %73, %85) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %87 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %88 = "llvm.insertelement"(%86, %2, %87) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %89 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %90 = "llvm.insertelement"(%88, %2, %89) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %91 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %92 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %93 = "llvm.insertelement"(%91, %2, %92) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %94 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %95 = "llvm.insertelement"(%93, %2, %94) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %96 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %97 = "llvm.insertelement"(%95, %73, %96) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %98 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %99 = "llvm.insertelement"(%97, %73, %98) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %100 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %101 = "llvm.insertelement"(%99, %2, %100) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %102 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %103 = "llvm.insertelement"(%101, %2, %102) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %104 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %105 = "llvm.insertelement"(%103, %73, %104) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %106 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %107 = "llvm.insertelement"(%105, %73, %106) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %108 = "llvm.mlir.constant"() <{value = dense<19> : vector<4xi64>}> : () -> vector<4xi64>
    %109 = "llvm.mlir.constant"() <{value = dense<1> : vector<8xi32>}> : () -> vector<8xi32>
    %110 = "llvm.mlir.constant"() <{value = dense<4294967295> : vector<4xi64>}> : () -> vector<4xi64>
    %111 = "llvm.mlir.constant"() <{value = dense<26> : vector<4xi64>}> : () -> vector<4xi64>
    %112 = "llvm.mlir.constant"() <{value = dense<67108863> : vector<4xi64>}> : () -> vector<4xi64>
    %113 = "llvm.mlir.constant"() <{value = dense<25> : vector<4xi64>}> : () -> vector<4xi64>
    %114 = "llvm.mlir.constant"() <{value = dense<33554431> : vector<4xi64>}> : () -> vector<4xi64>
    %115 = "llvm.mlir.constant"() <{value = dense<51> : vector<4xi64>}> : () -> vector<4xi64>
    %116 = "llvm.mlir.constant"() <{value = 67108863 : i32}> : () -> i32
    %117 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %118 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %119 = "llvm.insertelement"(%117, %116, %118) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %120 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %121 = "llvm.insertelement"(%119, %2, %120) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %122 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %123 = "llvm.insertelement"(%121, %116, %122) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %124 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %125 = "llvm.insertelement"(%123, %2, %124) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %126 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %127 = "llvm.insertelement"(%125, %116, %126) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %128 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %129 = "llvm.insertelement"(%127, %2, %128) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %130 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %131 = "llvm.insertelement"(%129, %116, %130) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %132 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %133 = "llvm.insertelement"(%131, %2, %132) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %134 = "llvm.mlir.constant"() <{value = 33554431 : i32}> : () -> i32
    %135 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %136 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %137 = "llvm.insertelement"(%135, %134, %136) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %138 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %139 = "llvm.insertelement"(%137, %2, %138) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %140 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %141 = "llvm.insertelement"(%139, %134, %140) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %142 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %143 = "llvm.insertelement"(%141, %2, %142) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %144 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %145 = "llvm.insertelement"(%143, %134, %144) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %146 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %147 = "llvm.insertelement"(%145, %2, %146) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %148 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %149 = "llvm.insertelement"(%147, %134, %148) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %150 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %151 = "llvm.insertelement"(%149, %2, %150) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %152 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %153 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %154 = "llvm.insertelement"(%152, %3, %153) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %155 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %156 = "llvm.insertelement"(%154, %2, %155) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %157 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %158 = "llvm.insertelement"(%156, %1, %157) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %159 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %160 = "llvm.insertelement"(%158, %2, %159) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %161 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %162 = "llvm.insertelement"(%160, %3, %161) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %163 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %164 = "llvm.insertelement"(%162, %2, %163) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %165 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %166 = "llvm.insertelement"(%164, %1, %165) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %167 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %168 = "llvm.insertelement"(%166, %2, %167) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %169 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %170 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %171 = "llvm.insertelement"(%169, %21, %170) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %172 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %173 = "llvm.insertelement"(%171, %2, %172) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %174 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %175 = "llvm.insertelement"(%173, %1, %174) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %176 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %177 = "llvm.insertelement"(%175, %2, %176) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %178 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %179 = "llvm.insertelement"(%177, %21, %178) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %180 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %181 = "llvm.insertelement"(%179, %2, %180) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %182 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %183 = "llvm.insertelement"(%181, %1, %182) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %184 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %185 = "llvm.insertelement"(%183, %2, %184) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %186 = "llvm.bitcast"(%arg5) : (vector<4xi64>) -> vector<8xi32>
    %187 = "llvm.bitcast"(%arg6) : (vector<4xi64>) -> vector<8xi32>
    %188 = "llvm.bitcast"(%arg7) : (vector<4xi64>) -> vector<8xi32>
    %189 = "llvm.bitcast"(%arg8) : (vector<4xi64>) -> vector<8xi32>
    %190 = "llvm.shufflevector"(%186, %0) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %191 = "llvm.shufflevector"(%187, %0) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %192 = "llvm.shufflevector"(%188, %0) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %193 = "llvm.shufflevector"(%189, %0) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %194 = "llvm.bitcast"(%arg9) : (vector<4xi64>) -> vector<8xi32>
    %195 = "llvm.shufflevector"(%194, %0) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %196 = "llvm.sub"(%20, %190) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %197 = "llvm.sub"(%38, %191) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %198 = "llvm.sub"(%38, %192) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %199 = "llvm.sub"(%38, %193) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %200 = "llvm.sub"(%38, %195) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %201 = "llvm.shufflevector"(%190, %196) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %202 = "llvm.shufflevector"(%191, %197) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %203 = "llvm.shufflevector"(%192, %198) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %204 = "llvm.shufflevector"(%193, %199) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %205 = "llvm.shufflevector"(%195, %200) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %206 = "llvm.bitcast"(%arg0) : (vector<4xi64>) -> vector<8xi32>
    %207 = "llvm.bitcast"(%arg1) : (vector<4xi64>) -> vector<8xi32>
    %208 = "llvm.bitcast"(%arg2) : (vector<4xi64>) -> vector<8xi32>
    %209 = "llvm.bitcast"(%arg3) : (vector<4xi64>) -> vector<8xi32>
    %210 = "llvm.shufflevector"(%206, %0) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %211 = "llvm.shufflevector"(%207, %0) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %212 = "llvm.shufflevector"(%208, %0) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %213 = "llvm.shufflevector"(%209, %0) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %214 = "llvm.bitcast"(%arg4) : (vector<4xi64>) -> vector<8xi32>
    %215 = "llvm.shufflevector"(%214, %0) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %216 = "llvm.sub"(%55, %206) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %217 = "llvm.sub"(%72, %207) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %218 = "llvm.sub"(%72, %208) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %219 = "llvm.sub"(%72, %209) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %220 = "llvm.sub"(%72, %214) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %221 = "llvm.shufflevector"(%216, %206) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %222 = "llvm.shufflevector"(%217, %207) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %223 = "llvm.shufflevector"(%218, %208) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %224 = "llvm.shufflevector"(%219, %209) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %225 = "llvm.shufflevector"(%220, %214) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %226 = "llvm.add"(%221, %210) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %227 = "llvm.add"(%222, %211) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %228 = "llvm.add"(%223, %212) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %229 = "llvm.add"(%224, %213) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %230 = "llvm.add"(%225, %215) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %231 = "llvm.shufflevector"(%226, %206) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %232 = "llvm.shufflevector"(%227, %207) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %233 = "llvm.shufflevector"(%228, %208) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %234 = "llvm.shufflevector"(%229, %209) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %235 = "llvm.shufflevector"(%230, %214) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %236 = "llvm.shufflevector"(%231, %90) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %237 = "llvm.shufflevector"(%231, %107) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %238 = "llvm.bitcast"(%236) : (vector<8xi32>) -> vector<4xi64>
    %239 = "llvm.bitcast"(%237) : (vector<8xi32>) -> vector<4xi64>
    %240 = "llvm.shufflevector"(%232, %90) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %241 = "llvm.shufflevector"(%232, %107) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %242 = "llvm.bitcast"(%240) : (vector<8xi32>) -> vector<4xi64>
    %243 = "llvm.bitcast"(%241) : (vector<8xi32>) -> vector<4xi64>
    %244 = "llvm.shufflevector"(%233, %90) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %245 = "llvm.shufflevector"(%233, %107) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %246 = "llvm.bitcast"(%244) : (vector<8xi32>) -> vector<4xi64>
    %247 = "llvm.bitcast"(%245) : (vector<8xi32>) -> vector<4xi64>
    %248 = "llvm.shufflevector"(%234, %90) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %249 = "llvm.shufflevector"(%234, %107) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %250 = "llvm.bitcast"(%248) : (vector<8xi32>) -> vector<4xi64>
    %251 = "llvm.bitcast"(%249) : (vector<8xi32>) -> vector<4xi64>
    %252 = "llvm.shufflevector"(%235, %90) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %253 = "llvm.shufflevector"(%235, %107) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %254 = "llvm.bitcast"(%252) : (vector<8xi32>) -> vector<4xi64>
    %255 = "llvm.bitcast"(%253) : (vector<8xi32>) -> vector<4xi64>
    %256 = "llvm.shufflevector"(%201, %90) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %257 = "llvm.shufflevector"(%201, %107) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %258 = "llvm.bitcast"(%256) : (vector<8xi32>) -> vector<4xi64>
    %259 = "llvm.bitcast"(%257) : (vector<8xi32>) -> vector<4xi64>
    %260 = "llvm.shufflevector"(%202, %90) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %261 = "llvm.shufflevector"(%202, %107) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %262 = "llvm.bitcast"(%260) : (vector<8xi32>) -> vector<4xi64>
    %263 = "llvm.bitcast"(%261) : (vector<8xi32>) -> vector<4xi64>
    %264 = "llvm.shufflevector"(%203, %90) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %265 = "llvm.shufflevector"(%203, %107) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %266 = "llvm.bitcast"(%264) : (vector<8xi32>) -> vector<4xi64>
    %267 = "llvm.bitcast"(%265) : (vector<8xi32>) -> vector<4xi64>
    %268 = "llvm.shufflevector"(%204, %90) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %269 = "llvm.shufflevector"(%204, %107) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %270 = "llvm.bitcast"(%268) : (vector<8xi32>) -> vector<4xi64>
    %271 = "llvm.bitcast"(%269) : (vector<8xi32>) -> vector<4xi64>
    %272 = "llvm.shufflevector"(%205, %90) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %273 = "llvm.shufflevector"(%205, %107) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %274 = "llvm.bitcast"(%272) : (vector<8xi32>) -> vector<4xi64>
    %275 = "llvm.bitcast"(%273) : (vector<8xi32>) -> vector<4xi64>
    %276 = "llvm.mul"(%259, %108) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %277 = "llvm.mul"(%262, %108) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %278 = "llvm.mul"(%263, %108) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %279 = "llvm.mul"(%266, %108) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %280 = "llvm.mul"(%267, %108) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %281 = "llvm.mul"(%270, %108) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %282 = "llvm.mul"(%271, %108) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %283 = "llvm.mul"(%274, %108) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %284 = "llvm.mul"(%275, %108) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %285 = "llvm.mul"(%258, %238) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %286 = "llvm.shl"(%237, %109) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %287 = "llvm.bitcast"(%286) : (vector<8xi32>) -> vector<4xi64>
    %288 = "llvm.and"(%284, %110) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %289 = "llvm.mul"(%288, %287) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %290 = "llvm.and"(%283, %110) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %291 = "llvm.mul"(%290, %242) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %292 = "llvm.shl"(%241, %109) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %293 = "llvm.bitcast"(%292) : (vector<8xi32>) -> vector<4xi64>
    %294 = "llvm.and"(%282, %110) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %295 = "llvm.mul"(%294, %293) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %296 = "llvm.and"(%281, %110) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %297 = "llvm.mul"(%296, %246) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %298 = "llvm.shl"(%245, %109) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %299 = "llvm.bitcast"(%298) : (vector<8xi32>) -> vector<4xi64>
    %300 = "llvm.and"(%280, %110) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %301 = "llvm.mul"(%300, %299) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %302 = "llvm.and"(%279, %110) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %303 = "llvm.mul"(%302, %250) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %304 = "llvm.shl"(%249, %109) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %305 = "llvm.bitcast"(%304) : (vector<8xi32>) -> vector<4xi64>
    %306 = "llvm.and"(%278, %110) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %307 = "llvm.mul"(%306, %305) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %308 = "llvm.and"(%277, %110) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %309 = "llvm.mul"(%308, %254) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %310 = "llvm.shl"(%253, %109) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %311 = "llvm.bitcast"(%310) : (vector<8xi32>) -> vector<4xi64>
    %312 = "llvm.and"(%276, %110) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %313 = "llvm.mul"(%312, %311) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %314 = "llvm.add"(%313, %285) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %315 = "llvm.add"(%314, %309) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %316 = "llvm.add"(%315, %307) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %317 = "llvm.add"(%316, %303) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %318 = "llvm.add"(%317, %301) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %319 = "llvm.add"(%318, %297) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %320 = "llvm.add"(%319, %295) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %321 = "llvm.add"(%320, %291) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %322 = "llvm.add"(%321, %289) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %323 = "llvm.mul"(%259, %238) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %324 = "llvm.mul"(%258, %239) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %325 = "llvm.mul"(%288, %242) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %326 = "llvm.mul"(%290, %243) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %327 = "llvm.mul"(%294, %246) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %328 = "llvm.mul"(%296, %247) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %329 = "llvm.mul"(%300, %250) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %330 = "llvm.mul"(%302, %251) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %331 = "llvm.mul"(%306, %254) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %332 = "llvm.mul"(%308, %255) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %333 = "llvm.mul"(%262, %238) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %334 = "llvm.mul"(%259, %287) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %335 = "llvm.mul"(%258, %242) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %336 = "llvm.mul"(%288, %293) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %337 = "llvm.mul"(%290, %246) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %338 = "llvm.mul"(%294, %299) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %339 = "llvm.mul"(%296, %250) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %340 = "llvm.mul"(%300, %305) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %341 = "llvm.mul"(%302, %254) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %342 = "llvm.mul"(%306, %311) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %343 = "llvm.mul"(%263, %238) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %344 = "llvm.mul"(%262, %239) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %345 = "llvm.mul"(%259, %242) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %346 = "llvm.mul"(%258, %243) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %347 = "llvm.mul"(%288, %246) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %348 = "llvm.mul"(%290, %247) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %349 = "llvm.mul"(%294, %250) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %350 = "llvm.mul"(%296, %251) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %351 = "llvm.mul"(%300, %254) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %352 = "llvm.mul"(%302, %255) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %353 = "llvm.mul"(%266, %238) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %354 = "llvm.mul"(%263, %287) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %355 = "llvm.mul"(%262, %242) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %356 = "llvm.mul"(%259, %293) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %357 = "llvm.mul"(%258, %246) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %358 = "llvm.mul"(%288, %299) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %359 = "llvm.mul"(%290, %250) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %360 = "llvm.mul"(%294, %305) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %361 = "llvm.mul"(%296, %254) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %362 = "llvm.mul"(%300, %311) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %363 = "llvm.add"(%357, %356) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %364 = "llvm.add"(%363, %355) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %365 = "llvm.add"(%364, %354) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %366 = "llvm.add"(%365, %353) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %367 = "llvm.add"(%366, %362) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %368 = "llvm.add"(%367, %361) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %369 = "llvm.add"(%368, %360) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %370 = "llvm.add"(%369, %359) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %371 = "llvm.add"(%370, %358) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %372 = "llvm.mul"(%267, %238) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %373 = "llvm.mul"(%266, %239) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %374 = "llvm.mul"(%263, %242) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %375 = "llvm.mul"(%262, %243) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %376 = "llvm.mul"(%259, %246) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %377 = "llvm.mul"(%258, %247) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %378 = "llvm.mul"(%288, %250) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %379 = "llvm.mul"(%290, %251) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %380 = "llvm.mul"(%294, %254) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %381 = "llvm.mul"(%296, %255) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %382 = "llvm.mul"(%270, %238) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %383 = "llvm.mul"(%267, %287) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %384 = "llvm.mul"(%266, %242) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %385 = "llvm.mul"(%263, %293) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %386 = "llvm.mul"(%262, %246) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %387 = "llvm.mul"(%259, %299) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %388 = "llvm.mul"(%258, %250) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %389 = "llvm.mul"(%288, %305) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %390 = "llvm.mul"(%290, %254) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %391 = "llvm.mul"(%294, %311) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %392 = "llvm.mul"(%271, %238) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %393 = "llvm.mul"(%270, %239) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %394 = "llvm.mul"(%267, %242) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %395 = "llvm.mul"(%266, %243) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %396 = "llvm.mul"(%263, %246) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %397 = "llvm.mul"(%262, %247) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %398 = "llvm.mul"(%259, %250) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %399 = "llvm.mul"(%258, %251) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %400 = "llvm.mul"(%288, %254) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %401 = "llvm.mul"(%290, %255) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %402 = "llvm.mul"(%274, %238) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %403 = "llvm.mul"(%271, %287) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %404 = "llvm.mul"(%270, %242) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %405 = "llvm.mul"(%267, %293) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %406 = "llvm.mul"(%266, %246) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %407 = "llvm.mul"(%263, %299) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %408 = "llvm.mul"(%262, %250) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %409 = "llvm.mul"(%259, %305) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %410 = "llvm.mul"(%258, %254) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %411 = "llvm.mul"(%288, %311) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %412 = "llvm.mul"(%275, %238) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %413 = "llvm.mul"(%274, %239) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %414 = "llvm.mul"(%271, %242) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %415 = "llvm.mul"(%270, %243) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %416 = "llvm.mul"(%267, %246) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %417 = "llvm.mul"(%266, %247) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %418 = "llvm.mul"(%263, %250) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %419 = "llvm.mul"(%262, %251) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %420 = "llvm.mul"(%259, %254) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %421 = "llvm.mul"(%258, %255) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %422 = "llvm.lshr"(%322, %111) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %423 = "llvm.add"(%324, %323) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %424 = "llvm.add"(%423, %331) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %425 = "llvm.add"(%424, %332) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %426 = "llvm.add"(%425, %329) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %427 = "llvm.add"(%426, %330) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %428 = "llvm.add"(%427, %327) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %429 = "llvm.add"(%428, %328) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %430 = "llvm.add"(%429, %325) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %431 = "llvm.add"(%430, %326) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %432 = "llvm.add"(%431, %422) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %433 = "llvm.and"(%322, %112) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %434 = "llvm.lshr"(%371, %111) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %435 = "llvm.add"(%377, %376) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %436 = "llvm.add"(%435, %374) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %437 = "llvm.add"(%436, %375) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %438 = "llvm.add"(%437, %372) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %439 = "llvm.add"(%438, %373) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %440 = "llvm.add"(%439, %380) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %441 = "llvm.add"(%440, %381) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %442 = "llvm.add"(%441, %378) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %443 = "llvm.add"(%442, %379) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %444 = "llvm.add"(%443, %434) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %445 = "llvm.and"(%371, %112) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %446 = "llvm.lshr"(%432, %113) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %447 = "llvm.add"(%335, %334) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %448 = "llvm.add"(%447, %333) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %449 = "llvm.add"(%448, %342) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %450 = "llvm.add"(%449, %341) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %451 = "llvm.add"(%450, %340) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %452 = "llvm.add"(%451, %339) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %453 = "llvm.add"(%452, %338) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %454 = "llvm.add"(%453, %337) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %455 = "llvm.add"(%454, %336) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %456 = "llvm.add"(%455, %446) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %457 = "llvm.and"(%432, %114) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %458 = "llvm.lshr"(%444, %113) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %459 = "llvm.add"(%388, %387) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %460 = "llvm.add"(%459, %385) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %461 = "llvm.add"(%460, %386) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %462 = "llvm.add"(%461, %384) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %463 = "llvm.add"(%462, %383) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %464 = "llvm.add"(%463, %382) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %465 = "llvm.add"(%464, %391) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %466 = "llvm.add"(%465, %390) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %467 = "llvm.add"(%466, %389) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %468 = "llvm.add"(%467, %458) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %469 = "llvm.and"(%444, %114) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %470 = "llvm.lshr"(%456, %111) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %471 = "llvm.add"(%346, %345) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %472 = "llvm.add"(%471, %343) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %473 = "llvm.add"(%472, %344) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %474 = "llvm.add"(%473, %351) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %475 = "llvm.add"(%474, %352) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %476 = "llvm.add"(%475, %349) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %477 = "llvm.add"(%476, %350) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %478 = "llvm.add"(%477, %347) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %479 = "llvm.add"(%478, %348) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %480 = "llvm.add"(%479, %470) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %481 = "llvm.lshr"(%468, %111) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %482 = "llvm.add"(%399, %398) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %483 = "llvm.add"(%482, %396) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %484 = "llvm.add"(%483, %397) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %485 = "llvm.add"(%484, %394) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %486 = "llvm.add"(%485, %395) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %487 = "llvm.add"(%486, %392) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %488 = "llvm.add"(%487, %393) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %489 = "llvm.add"(%488, %400) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %490 = "llvm.add"(%489, %401) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %491 = "llvm.add"(%490, %481) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %492 = "llvm.lshr"(%480, %113) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %493 = "llvm.add"(%492, %445) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %494 = "llvm.lshr"(%491, %113) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %495 = "llvm.add"(%409, %410) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %496 = "llvm.add"(%495, %408) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %497 = "llvm.add"(%496, %407) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %498 = "llvm.add"(%497, %406) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %499 = "llvm.add"(%498, %405) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %500 = "llvm.add"(%499, %404) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %501 = "llvm.add"(%500, %403) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %502 = "llvm.add"(%501, %402) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %503 = "llvm.add"(%502, %411) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %504 = "llvm.add"(%503, %494) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %505 = "llvm.lshr"(%493, %111) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %506 = "llvm.add"(%505, %469) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %507 = "llvm.lshr"(%504, %111) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %508 = "llvm.add"(%421, %420) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %509 = "llvm.add"(%508, %418) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %510 = "llvm.add"(%509, %419) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %511 = "llvm.add"(%510, %416) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %512 = "llvm.add"(%511, %417) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %513 = "llvm.add"(%512, %414) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %514 = "llvm.add"(%513, %415) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %515 = "llvm.add"(%514, %412) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %516 = "llvm.add"(%515, %413) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %517 = "llvm.add"(%516, %507) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %518 = "llvm.lshr"(%517, %113) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %519 = "llvm.and"(%518, %112) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %520 = "llvm.lshr"(%517, %115) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %521 = "llvm.mul"(%519, %108) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %522 = "llvm.mul"(%520, %108) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %523 = "llvm.add"(%521, %433) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %524 = "llvm.add"(%522, %457) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %525 = "llvm.lshr"(%523, %111) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %526 = "llvm.add"(%524, %525) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %527 = "llvm.bitcast"(%523) : (vector<4xi64>) -> vector<8xi32>
    %528 = "llvm.and"(%527, %133) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %529 = "llvm.bitcast"(%526) : (vector<4xi64>) -> vector<8xi32>
    %530 = "llvm.shufflevector"(%528, %529) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %531 = "llvm.bitcast"(%456) : (vector<4xi64>) -> vector<8xi32>
    %532 = "llvm.and"(%531, %133) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %533 = "llvm.bitcast"(%480) : (vector<4xi64>) -> vector<8xi32>
    %534 = "llvm.and"(%533, %151) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %535 = "llvm.shufflevector"(%532, %534) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %536 = "llvm.bitcast"(%506) : (vector<4xi64>) -> vector<8xi32>
    %537 = "llvm.bitcast"(%493) : (vector<4xi64>) -> vector<8xi32>
    %538 = "llvm.and"(%537, %133) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %539 = "llvm.shufflevector"(%538, %536) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %540 = "llvm.bitcast"(%468) : (vector<4xi64>) -> vector<8xi32>
    %541 = "llvm.and"(%540, %133) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %542 = "llvm.bitcast"(%491) : (vector<4xi64>) -> vector<8xi32>
    %543 = "llvm.and"(%542, %151) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %544 = "llvm.shufflevector"(%541, %543) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %545 = "llvm.bitcast"(%504) : (vector<4xi64>) -> vector<8xi32>
    %546 = "llvm.and"(%545, %133) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %547 = "llvm.bitcast"(%517) : (vector<4xi64>) -> vector<8xi32>
    %548 = "llvm.and"(%547, %151) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %549 = "llvm.shufflevector"(%546, %548) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %550 = "llvm.shufflevector"(%530, %0) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %551 = "llvm.shufflevector"(%535, %0) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %552 = "llvm.shufflevector"(%539, %0) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %553 = "llvm.shufflevector"(%544, %0) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %554 = "llvm.shufflevector"(%549, %0) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %555 = "llvm.shufflevector"(%530, %0) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %556 = "llvm.shufflevector"(%535, %0) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %557 = "llvm.shufflevector"(%539, %0) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %558 = "llvm.shufflevector"(%544, %0) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %559 = "llvm.shufflevector"(%549, %0) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %560 = "llvm.sub"(%168, %550) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %561 = "llvm.sub"(%185, %551) <{overflowFlags = 1 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %562 = "llvm.sub"(%185, %552) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %563 = "llvm.sub"(%185, %553) <{overflowFlags = 1 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %564 = "llvm.sub"(%185, %554) <{overflowFlags = 1 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %565 = "llvm.shufflevector"(%560, %550) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %566 = "llvm.shufflevector"(%561, %551) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %567 = "llvm.shufflevector"(%562, %552) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %568 = "llvm.shufflevector"(%563, %553) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %569 = "llvm.shufflevector"(%564, %554) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %570 = "llvm.add"(%565, %555) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %571 = "llvm.add"(%566, %556) <{overflowFlags = 1 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %572 = "llvm.add"(%567, %557) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %573 = "llvm.add"(%568, %558) <{overflowFlags = 1 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %574 = "llvm.add"(%569, %559) <{overflowFlags = 1 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %575 = "llvm.shufflevector"(%570, %0) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %576 = "llvm.shufflevector"(%571, %0) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %577 = "llvm.shufflevector"(%572, %0) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %578 = "llvm.shufflevector"(%573, %0) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %579 = "llvm.shufflevector"(%574, %0) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %580 = "llvm.shufflevector"(%570, %0) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %581 = "llvm.shufflevector"(%571, %0) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %582 = "llvm.shufflevector"(%572, %0) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %583 = "llvm.shufflevector"(%573, %0) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %584 = "llvm.shufflevector"(%574, %0) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %585 = "llvm.shufflevector"(%575, %90) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %586 = "llvm.shufflevector"(%575, %107) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %587 = "llvm.bitcast"(%585) : (vector<8xi32>) -> vector<4xi64>
    %588 = "llvm.bitcast"(%586) : (vector<8xi32>) -> vector<4xi64>
    %589 = "llvm.shufflevector"(%576, %90) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %590 = "llvm.shufflevector"(%576, %107) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %591 = "llvm.bitcast"(%589) : (vector<8xi32>) -> vector<4xi64>
    %592 = "llvm.bitcast"(%590) : (vector<8xi32>) -> vector<4xi64>
    %593 = "llvm.shufflevector"(%577, %90) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %594 = "llvm.shufflevector"(%577, %107) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %595 = "llvm.bitcast"(%593) : (vector<8xi32>) -> vector<4xi64>
    %596 = "llvm.bitcast"(%594) : (vector<8xi32>) -> vector<4xi64>
    %597 = "llvm.shufflevector"(%578, %90) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %598 = "llvm.shufflevector"(%578, %107) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %599 = "llvm.bitcast"(%597) : (vector<8xi32>) -> vector<4xi64>
    %600 = "llvm.bitcast"(%598) : (vector<8xi32>) -> vector<4xi64>
    %601 = "llvm.shufflevector"(%579, %90) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %602 = "llvm.shufflevector"(%579, %107) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %603 = "llvm.bitcast"(%601) : (vector<8xi32>) -> vector<4xi64>
    %604 = "llvm.bitcast"(%602) : (vector<8xi32>) -> vector<4xi64>
    %605 = "llvm.shufflevector"(%580, %90) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %606 = "llvm.shufflevector"(%580, %107) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %607 = "llvm.bitcast"(%605) : (vector<8xi32>) -> vector<4xi64>
    %608 = "llvm.bitcast"(%606) : (vector<8xi32>) -> vector<4xi64>
    %609 = "llvm.shufflevector"(%581, %90) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %610 = "llvm.shufflevector"(%581, %107) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %611 = "llvm.bitcast"(%609) : (vector<8xi32>) -> vector<4xi64>
    %612 = "llvm.bitcast"(%610) : (vector<8xi32>) -> vector<4xi64>
    %613 = "llvm.shufflevector"(%582, %90) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %614 = "llvm.shufflevector"(%582, %107) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %615 = "llvm.bitcast"(%613) : (vector<8xi32>) -> vector<4xi64>
    %616 = "llvm.bitcast"(%614) : (vector<8xi32>) -> vector<4xi64>
    %617 = "llvm.shufflevector"(%583, %90) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %618 = "llvm.shufflevector"(%583, %107) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %619 = "llvm.bitcast"(%617) : (vector<8xi32>) -> vector<4xi64>
    %620 = "llvm.bitcast"(%618) : (vector<8xi32>) -> vector<4xi64>
    %621 = "llvm.shufflevector"(%584, %90) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %622 = "llvm.shufflevector"(%584, %107) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %623 = "llvm.bitcast"(%621) : (vector<8xi32>) -> vector<4xi64>
    %624 = "llvm.bitcast"(%622) : (vector<8xi32>) -> vector<4xi64>
    %625 = "llvm.mul"(%608, %108) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %626 = "llvm.mul"(%611, %108) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %627 = "llvm.mul"(%612, %108) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %628 = "llvm.mul"(%615, %108) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %629 = "llvm.mul"(%616, %108) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %630 = "llvm.mul"(%619, %108) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %631 = "llvm.mul"(%620, %108) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %632 = "llvm.mul"(%623, %108) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %633 = "llvm.mul"(%624, %108) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %634 = "llvm.mul"(%607, %587) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %635 = "llvm.shl"(%586, %109) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %636 = "llvm.bitcast"(%635) : (vector<8xi32>) -> vector<4xi64>
    %637 = "llvm.and"(%633, %110) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %638 = "llvm.mul"(%637, %636) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %639 = "llvm.and"(%632, %110) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %640 = "llvm.mul"(%639, %591) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %641 = "llvm.shl"(%590, %109) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %642 = "llvm.bitcast"(%641) : (vector<8xi32>) -> vector<4xi64>
    %643 = "llvm.and"(%631, %110) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %644 = "llvm.mul"(%643, %642) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %645 = "llvm.and"(%630, %110) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %646 = "llvm.mul"(%645, %595) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %647 = "llvm.shl"(%594, %109) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %648 = "llvm.bitcast"(%647) : (vector<8xi32>) -> vector<4xi64>
    %649 = "llvm.and"(%629, %110) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %650 = "llvm.mul"(%649, %648) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %651 = "llvm.and"(%628, %110) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %652 = "llvm.mul"(%651, %599) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %653 = "llvm.shl"(%598, %109) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %654 = "llvm.bitcast"(%653) : (vector<8xi32>) -> vector<4xi64>
    %655 = "llvm.and"(%627, %110) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %656 = "llvm.mul"(%655, %654) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %657 = "llvm.and"(%626, %110) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %658 = "llvm.mul"(%657, %603) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %659 = "llvm.shl"(%602, %109) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %660 = "llvm.bitcast"(%659) : (vector<8xi32>) -> vector<4xi64>
    %661 = "llvm.and"(%625, %110) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %662 = "llvm.mul"(%661, %660) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %663 = "llvm.add"(%662, %634) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %664 = "llvm.add"(%663, %658) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %665 = "llvm.add"(%664, %656) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %666 = "llvm.add"(%665, %652) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %667 = "llvm.add"(%666, %650) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %668 = "llvm.add"(%667, %646) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %669 = "llvm.add"(%668, %644) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %670 = "llvm.add"(%669, %640) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %671 = "llvm.add"(%670, %638) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %672 = "llvm.mul"(%608, %587) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %673 = "llvm.mul"(%607, %588) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %674 = "llvm.mul"(%633, %591) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %675 = "llvm.mul"(%632, %592) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %676 = "llvm.mul"(%643, %595) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %677 = "llvm.mul"(%645, %596) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %678 = "llvm.mul"(%649, %599) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %679 = "llvm.mul"(%651, %600) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %680 = "llvm.mul"(%655, %603) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %681 = "llvm.mul"(%657, %604) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %682 = "llvm.mul"(%615, %587) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %683 = "llvm.mul"(%612, %636) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %684 = "llvm.mul"(%611, %591) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %685 = "llvm.mul"(%608, %642) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %686 = "llvm.mul"(%607, %595) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %687 = "llvm.mul"(%637, %648) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %688 = "llvm.mul"(%639, %599) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %689 = "llvm.mul"(%643, %654) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %690 = "llvm.mul"(%645, %603) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %691 = "llvm.mul"(%649, %660) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %692 = "llvm.add"(%686, %685) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %693 = "llvm.add"(%692, %684) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %694 = "llvm.add"(%693, %683) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %695 = "llvm.add"(%694, %682) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %696 = "llvm.add"(%695, %691) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %697 = "llvm.add"(%696, %690) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %698 = "llvm.add"(%697, %689) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %699 = "llvm.add"(%698, %688) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %700 = "llvm.add"(%699, %687) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %701 = "llvm.mul"(%616, %587) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %702 = "llvm.mul"(%615, %588) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %703 = "llvm.mul"(%612, %591) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %704 = "llvm.mul"(%611, %592) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %705 = "llvm.mul"(%608, %595) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %706 = "llvm.mul"(%607, %596) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %707 = "llvm.mul"(%637, %599) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %708 = "llvm.mul"(%639, %600) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %709 = "llvm.mul"(%643, %603) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %710 = "llvm.mul"(%645, %604) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %711 = "llvm.mul"(%619, %587) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %712 = "llvm.mul"(%616, %636) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %713 = "llvm.mul"(%615, %591) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %714 = "llvm.mul"(%612, %642) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %715 = "llvm.mul"(%611, %595) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %716 = "llvm.mul"(%608, %648) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %717 = "llvm.mul"(%607, %599) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %718 = "llvm.mul"(%637, %654) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %719 = "llvm.mul"(%639, %603) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %720 = "llvm.mul"(%643, %660) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %721 = "llvm.mul"(%620, %587) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %722 = "llvm.mul"(%619, %588) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %723 = "llvm.mul"(%616, %591) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %724 = "llvm.mul"(%615, %592) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %725 = "llvm.mul"(%612, %595) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %726 = "llvm.mul"(%611, %596) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %727 = "llvm.mul"(%608, %599) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %728 = "llvm.mul"(%607, %600) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %729 = "llvm.mul"(%637, %603) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %730 = "llvm.mul"(%639, %604) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %731 = "llvm.mul"(%623, %587) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %732 = "llvm.mul"(%620, %636) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %733 = "llvm.mul"(%619, %591) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %734 = "llvm.mul"(%616, %642) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %735 = "llvm.mul"(%615, %595) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %736 = "llvm.mul"(%612, %648) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %737 = "llvm.mul"(%611, %599) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %738 = "llvm.mul"(%608, %654) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %739 = "llvm.mul"(%607, %603) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %740 = "llvm.mul"(%637, %660) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %741 = "llvm.mul"(%624, %587) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %742 = "llvm.mul"(%623, %588) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %743 = "llvm.mul"(%620, %591) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %744 = "llvm.mul"(%619, %592) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %745 = "llvm.mul"(%616, %595) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %746 = "llvm.mul"(%615, %596) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %747 = "llvm.mul"(%612, %599) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %748 = "llvm.mul"(%611, %600) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %749 = "llvm.mul"(%608, %603) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %750 = "llvm.mul"(%607, %604) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %751 = "llvm.lshr"(%671, %111) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %752 = "llvm.add"(%673, %672) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %753 = "llvm.add"(%752, %680) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %754 = "llvm.add"(%753, %681) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %755 = "llvm.add"(%754, %678) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %756 = "llvm.add"(%755, %679) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %757 = "llvm.add"(%756, %676) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %758 = "llvm.add"(%757, %677) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %759 = "llvm.add"(%758, %674) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %760 = "llvm.add"(%759, %675) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %761 = "llvm.add"(%760, %751) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %762 = "llvm.and"(%671, %112) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %763 = "llvm.lshr"(%700, %111) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %764 = "llvm.add"(%706, %705) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %765 = "llvm.add"(%764, %703) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %766 = "llvm.add"(%765, %704) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %767 = "llvm.add"(%766, %701) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %768 = "llvm.add"(%767, %702) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %769 = "llvm.add"(%768, %709) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %770 = "llvm.add"(%769, %710) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %771 = "llvm.add"(%770, %707) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %772 = "llvm.add"(%771, %708) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %773 = "llvm.add"(%772, %763) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %774 = "llvm.and"(%761, %114) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %775 = "llvm.lshr"(%773, %113) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %776 = "llvm.add"(%717, %716) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %777 = "llvm.add"(%776, %714) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %778 = "llvm.add"(%777, %715) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %779 = "llvm.add"(%778, %713) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %780 = "llvm.add"(%779, %712) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %781 = "llvm.add"(%780, %711) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %782 = "llvm.add"(%781, %720) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %783 = "llvm.add"(%782, %719) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %784 = "llvm.add"(%783, %718) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %785 = "llvm.add"(%784, %775) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %786 = "llvm.lshr"(%785, %111) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %787 = "llvm.add"(%728, %727) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %788 = "llvm.add"(%787, %725) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %789 = "llvm.add"(%788, %726) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %790 = "llvm.add"(%789, %723) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %791 = "llvm.add"(%790, %724) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %792 = "llvm.add"(%791, %721) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %793 = "llvm.add"(%792, %722) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %794 = "llvm.add"(%793, %729) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %795 = "llvm.add"(%794, %730) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %796 = "llvm.add"(%795, %786) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %797 = "llvm.lshr"(%796, %113) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %798 = "llvm.add"(%738, %739) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %799 = "llvm.add"(%798, %737) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %800 = "llvm.add"(%799, %736) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %801 = "llvm.add"(%800, %735) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %802 = "llvm.add"(%801, %734) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %803 = "llvm.add"(%802, %733) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %804 = "llvm.add"(%803, %732) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %805 = "llvm.add"(%804, %731) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %806 = "llvm.add"(%805, %740) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %807 = "llvm.add"(%806, %797) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %808 = "llvm.lshr"(%807, %111) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %809 = "llvm.add"(%750, %749) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %810 = "llvm.add"(%809, %747) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %811 = "llvm.add"(%810, %748) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %812 = "llvm.add"(%811, %745) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %813 = "llvm.add"(%812, %746) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %814 = "llvm.add"(%813, %743) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %815 = "llvm.add"(%814, %744) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %816 = "llvm.add"(%815, %741) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %817 = "llvm.add"(%816, %742) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %818 = "llvm.add"(%817, %808) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %819 = "llvm.lshr"(%818, %113) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %820 = "llvm.and"(%819, %112) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %821 = "llvm.lshr"(%818, %115) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %822 = "llvm.mul"(%820, %108) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %823 = "llvm.mul"(%821, %108) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %824 = "llvm.add"(%822, %762) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %825 = "llvm.add"(%823, %774) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %826 = "llvm.lshr"(%824, %111) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %827 = "llvm.add"(%825, %826) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %828 = "llvm.bitcast"(%824) : (vector<4xi64>) -> vector<8xi32>
    %829 = "llvm.and"(%828, %133) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %830 = "llvm.bitcast"(%827) : (vector<4xi64>) -> vector<8xi32>
    %831 = "llvm.shufflevector"(%829, %830) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %832 = "llvm.bitcast"(%831) : (vector<8xi32>) -> vector<4xi64>
    "llvm.return"(%832) : (vector<4xi64>) -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

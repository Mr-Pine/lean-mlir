#alias_scope_domain = #llvm.alias_scope_domain<id = distinct[0]<>, description = "_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x48reduce64B1a_NtB2_17___Impl_reduce64__14__impl_reduce64">
#alias_scope = #llvm.alias_scope<id = distinct[1]<>, domain = #alias_scope_domain, description = "_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x48reduce64B1a_NtB2_17___Impl_reduce64__14__impl_reduce64: %_0">
#alias_scope1 = #llvm.alias_scope<id = distinct[2]<>, domain = #alias_scope_domain, description = "_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x48reduce64B1a_NtB2_17___Impl_reduce64__14__impl_reduce64: %z">
"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.noundef, llvm.sret = !llvm.array<160 x i8>, llvm.writeonly}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.noundef, llvm.readonly}], function_type = !llvm.func<void (ptr, ptr)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], sym_name = "_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x419square_and_negate_DB1a_NtB2_28___Impl_square_and_negate_D__25__impl_square_and_negate_D", target_cpu = "x86-64", target_features = #llvm.target_features<["+avx", "+avx2", "+sse", "+sse2", "+sse3", "+sse4.1", "+sse4.2", "+crc32", "+ssse3"]>, unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
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
    %36 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %37 = "llvm.mlir.constant"() <{value = 64 : i64}> : () -> i64
    %38 = "llvm.mlir.constant"() <{value = 96 : i64}> : () -> i64
    %39 = "llvm.mlir.constant"() <{value = 128 : i64}> : () -> i64
    %40 = "llvm.mlir.constant"() <{value = dense<1> : vector<8xi32>}> : () -> vector<8xi32>
    %41 = "llvm.mlir.constant"() <{value = dense<19> : vector<4xi64>}> : () -> vector<4xi64>
    %42 = "llvm.mlir.constant"() <{value = dense<4294967295> : vector<4xi64>}> : () -> vector<4xi64>
    %43 = "llvm.mlir.constant"() <{value = dense<1> : vector<4xi64>}> : () -> vector<4xi64>
    %44 = "llvm.mlir.constant"() <{value = 9223369425514659840 : i64}> : () -> i64
    %45 = "llvm.mlir.poison"() : () -> i64
    %46 = "llvm.mlir.undef"() : () -> vector<4xi64>
    %47 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %48 = "llvm.insertelement"(%46, %45, %47) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %49 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %50 = "llvm.insertelement"(%48, %45, %49) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %51 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %52 = "llvm.insertelement"(%50, %45, %51) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %53 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %54 = "llvm.insertelement"(%52, %44, %53) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %55 = "llvm.mlir.constant"() <{value = 4611685880988434432 : i64}> : () -> i64
    %56 = "llvm.mlir.undef"() : () -> vector<4xi64>
    %57 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %58 = "llvm.insertelement"(%56, %45, %57) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %59 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %60 = "llvm.insertelement"(%58, %45, %59) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %61 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %62 = "llvm.insertelement"(%60, %45, %61) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %63 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %64 = "llvm.insertelement"(%62, %55, %63) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %65 = "llvm.mlir.constant"() <{value = 9223371899415822336 : i64}> : () -> i64
    %66 = "llvm.mlir.undef"() : () -> vector<4xi64>
    %67 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %68 = "llvm.insertelement"(%66, %45, %67) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %69 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %70 = "llvm.insertelement"(%68, %45, %69) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %71 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %72 = "llvm.insertelement"(%70, %45, %71) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %73 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %74 = "llvm.insertelement"(%72, %65, %73) : (vector<4xi64>, i64, i32) -> vector<4xi64>
    %75 = "llvm.mlir.constant"() <{value = dense<26> : vector<4xi64>}> : () -> vector<4xi64>
    %76 = "llvm.mlir.constant"() <{value = dense<67108863> : vector<4xi64>}> : () -> vector<4xi64>
    %77 = "llvm.mlir.constant"() <{value = dense<25> : vector<4xi64>}> : () -> vector<4xi64>
    %78 = "llvm.mlir.constant"() <{value = dense<33554431> : vector<4xi64>}> : () -> vector<4xi64>
    %79 = "llvm.mlir.constant"() <{value = dense<51> : vector<4xi64>}> : () -> vector<4xi64>
    %80 = "llvm.mlir.constant"() <{value = 67108863 : i32}> : () -> i32
    %81 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %82 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %83 = "llvm.insertelement"(%81, %80, %82) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %84 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %85 = "llvm.insertelement"(%83, %0, %84) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %86 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %87 = "llvm.insertelement"(%85, %80, %86) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %88 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %89 = "llvm.insertelement"(%87, %0, %88) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %90 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %91 = "llvm.insertelement"(%89, %80, %90) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %92 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %93 = "llvm.insertelement"(%91, %0, %92) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %94 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %95 = "llvm.insertelement"(%93, %80, %94) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %96 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %97 = "llvm.insertelement"(%95, %0, %96) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %98 = "llvm.mlir.constant"() <{value = 33554431 : i32}> : () -> i32
    %99 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %100 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %101 = "llvm.insertelement"(%99, %98, %100) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %102 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %103 = "llvm.insertelement"(%101, %0, %102) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %104 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %105 = "llvm.insertelement"(%103, %98, %104) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %106 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %107 = "llvm.insertelement"(%105, %0, %106) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %108 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %109 = "llvm.insertelement"(%107, %98, %108) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %110 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %111 = "llvm.insertelement"(%109, %0, %110) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %112 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %113 = "llvm.insertelement"(%111, %98, %112) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %114 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %115 = "llvm.insertelement"(%113, %0, %114) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %116 = "llvm.load"(%arg1) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %117 = "llvm.shufflevector"(%116, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %118 = "llvm.shufflevector"(%116, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %119 = "llvm.bitcast"(%117) : (vector<8xi32>) -> vector<4xi64>
    %120 = "llvm.bitcast"(%118) : (vector<8xi32>) -> vector<4xi64>
    %121 = "llvm.getelementptr"(%arg1, %36) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %122 = "llvm.load"(%121) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %123 = "llvm.shufflevector"(%122, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %124 = "llvm.shufflevector"(%122, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %125 = "llvm.bitcast"(%123) : (vector<8xi32>) -> vector<4xi64>
    %126 = "llvm.bitcast"(%124) : (vector<8xi32>) -> vector<4xi64>
    %127 = "llvm.getelementptr"(%arg1, %37) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %128 = "llvm.load"(%127) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %129 = "llvm.shufflevector"(%128, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %130 = "llvm.shufflevector"(%128, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %131 = "llvm.bitcast"(%129) : (vector<8xi32>) -> vector<4xi64>
    %132 = "llvm.bitcast"(%130) : (vector<8xi32>) -> vector<4xi64>
    %133 = "llvm.getelementptr"(%arg1, %38) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %134 = "llvm.load"(%133) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %135 = "llvm.shufflevector"(%134, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %136 = "llvm.shufflevector"(%134, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %137 = "llvm.bitcast"(%135) : (vector<8xi32>) -> vector<4xi64>
    %138 = "llvm.bitcast"(%136) : (vector<8xi32>) -> vector<4xi64>
    %139 = "llvm.getelementptr"(%arg1, %39) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %140 = "llvm.load"(%139) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %141 = "llvm.shufflevector"(%140, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %142 = "llvm.shufflevector"(%140, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %143 = "llvm.bitcast"(%141) : (vector<8xi32>) -> vector<4xi64>
    %144 = "llvm.bitcast"(%142) : (vector<8xi32>) -> vector<4xi64>
    %145 = "llvm.shl"(%117, %40) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %146 = "llvm.bitcast"(%145) : (vector<8xi32>) -> vector<4xi64>
    %147 = "llvm.shl"(%118, %40) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %148 = "llvm.bitcast"(%147) : (vector<8xi32>) -> vector<4xi64>
    %149 = "llvm.shl"(%123, %40) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %150 = "llvm.bitcast"(%149) : (vector<8xi32>) -> vector<4xi64>
    %151 = "llvm.shl"(%124, %40) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %152 = "llvm.bitcast"(%151) : (vector<8xi32>) -> vector<4xi64>
    %153 = "llvm.shl"(%129, %40) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %154 = "llvm.bitcast"(%153) : (vector<8xi32>) -> vector<4xi64>
    %155 = "llvm.shl"(%130, %40) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %156 = "llvm.bitcast"(%155) : (vector<8xi32>) -> vector<4xi64>
    %157 = "llvm.shl"(%135, %40) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %158 = "llvm.bitcast"(%157) : (vector<8xi32>) -> vector<4xi64>
    %159 = "llvm.shl"(%136, %40) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %160 = "llvm.bitcast"(%159) : (vector<8xi32>) -> vector<4xi64>
    %161 = "llvm.mul"(%132, %41) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %162 = "llvm.mul"(%137, %41) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %163 = "llvm.mul"(%138, %41) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %164 = "llvm.mul"(%143, %41) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %165 = "llvm.mul"(%144, %41) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %166 = "llvm.mul"(%119, %119) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %167 = "llvm.and"(%164, %42) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %168 = "llvm.mul"(%167, %150) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %169 = "llvm.and"(%162, %42) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %170 = "llvm.mul"(%169, %154) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %171 = "llvm.and"(%165, %42) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %172 = "llvm.mul"(%171, %148) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %173 = "llvm.and"(%163, %42) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %174 = "llvm.mul"(%173, %152) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %175 = "llvm.and"(%161, %42) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %176 = "llvm.mul"(%175, %132) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %177 = "llvm.add"(%174, %176) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %178 = "llvm.add"(%177, %172) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %179 = "llvm.shl"(%178, %43) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %180 = "llvm.add"(%170, %166) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %181 = "llvm.add"(%180, %168) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %182 = "llvm.add"(%181, %179) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %183 = "llvm.mul"(%146, %120) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %184 = "llvm.mul"(%167, %152) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %185 = "llvm.mul"(%169, %156) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %186 = "llvm.mul"(%171, %125) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %187 = "llvm.mul"(%173, %131) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %188 = "llvm.add"(%186, %187) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %189 = "llvm.shl"(%188, %43) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %190 = "llvm.add"(%185, %183) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %191 = "llvm.add"(%190, %184) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %192 = "llvm.add"(%191, %189) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %193 = "llvm.mul"(%125, %146) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %194 = "llvm.mul"(%148, %120) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %195 = "llvm.add"(%194, %193) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %196 = "llvm.mul"(%167, %154) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %197 = "llvm.mul"(%169, %137) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %198 = "llvm.mul"(%171, %152) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %199 = "llvm.mul"(%173, %156) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %200 = "llvm.add"(%198, %199) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %201 = "llvm.shl"(%200, %43) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %202 = "llvm.add"(%195, %197) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %203 = "llvm.add"(%202, %196) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %204 = "llvm.add"(%203, %201) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %205 = "llvm.mul"(%126, %146) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %206 = "llvm.mul"(%125, %148) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %207 = "llvm.add"(%206, %205) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %208 = "llvm.mul"(%167, %156) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %209 = "llvm.add"(%207, %208) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %210 = "llvm.mul"(%171, %131) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %211 = "llvm.mul"(%173, %137) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %212 = "llvm.add"(%210, %211) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %213 = "llvm.shl"(%212, %43) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %214 = "llvm.add"(%209, %213) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %215 = "llvm.mul"(%131, %146) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %216 = "llvm.mul"(%152, %148) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %217 = "llvm.mul"(%125, %125) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %218 = "llvm.mul"(%167, %158) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %219 = "llvm.mul"(%171, %156) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %220 = "llvm.mul"(%173, %138) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %221 = "llvm.add"(%219, %220) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %222 = "llvm.shl"(%221, %43) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %223 = "llvm.add"(%215, %217) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %224 = "llvm.add"(%223, %216) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %225 = "llvm.add"(%224, %218) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %226 = "llvm.add"(%225, %222) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %227 = "llvm.mul"(%132, %146) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %228 = "llvm.mul"(%131, %148) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %229 = "llvm.add"(%228, %227) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %230 = "llvm.mul"(%150, %126) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %231 = "llvm.add"(%229, %230) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %232 = "llvm.mul"(%167, %160) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %233 = "llvm.add"(%231, %232) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %234 = "llvm.mul"(%171, %137) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %235 = "llvm.shl"(%234, %43) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %236 = "llvm.add"(%233, %235) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %237 = "llvm.mul"(%137, %146) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %238 = "llvm.mul"(%156, %148) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %239 = "llvm.mul"(%131, %150) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %240 = "llvm.mul"(%152, %126) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %241 = "llvm.mul"(%167, %143) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %242 = "llvm.mul"(%171, %160) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %243 = "llvm.shl"(%242, %43) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %244 = "llvm.add"(%240, %239) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %245 = "llvm.add"(%244, %237) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %246 = "llvm.add"(%245, %238) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %247 = "llvm.add"(%246, %241) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %248 = "llvm.add"(%247, %243) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %249 = "llvm.mul"(%138, %146) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %250 = "llvm.mul"(%137, %148) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %251 = "llvm.mul"(%132, %150) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %252 = "llvm.mul"(%131, %152) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %253 = "llvm.mul"(%171, %143) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %254 = "llvm.shl"(%253, %43) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %255 = "llvm.add"(%252, %251) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %256 = "llvm.add"(%255, %249) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %257 = "llvm.add"(%256, %250) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %258 = "llvm.add"(%257, %254) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %259 = "llvm.mul"(%143, %146) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %260 = "llvm.mul"(%160, %148) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %261 = "llvm.mul"(%137, %150) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %262 = "llvm.mul"(%156, %152) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %263 = "llvm.mul"(%131, %131) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %264 = "llvm.mul"(%171, %144) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %265 = "llvm.shl"(%264, %43) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %266 = "llvm.add"(%261, %263) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %267 = "llvm.add"(%266, %262) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %268 = "llvm.add"(%267, %259) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %269 = "llvm.add"(%268, %260) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %270 = "llvm.add"(%269, %265) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %271 = "llvm.mul"(%144, %146) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %272 = "llvm.mul"(%143, %148) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %273 = "llvm.mul"(%138, %150) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %274 = "llvm.mul"(%137, %152) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %275 = "llvm.mul"(%154, %132) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %276 = "llvm.add"(%274, %273) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %277 = "llvm.add"(%276, %275) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %278 = "llvm.add"(%277, %271) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %279 = "llvm.add"(%278, %272) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %280 = "llvm.sub"(%54, %182) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %281 = "llvm.shufflevector"(%182, %280) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %282 = "llvm.sub"(%64, %192) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %283 = "llvm.shufflevector"(%192, %282) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %284 = "llvm.sub"(%74, %204) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %285 = "llvm.shufflevector"(%204, %284) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %286 = "llvm.sub"(%64, %214) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %287 = "llvm.shufflevector"(%214, %286) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %288 = "llvm.sub"(%74, %226) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %289 = "llvm.shufflevector"(%226, %288) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %290 = "llvm.sub"(%64, %236) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %291 = "llvm.shufflevector"(%236, %290) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %292 = "llvm.sub"(%74, %248) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %293 = "llvm.shufflevector"(%248, %292) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %294 = "llvm.sub"(%64, %258) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %295 = "llvm.shufflevector"(%258, %294) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %296 = "llvm.sub"(%74, %270) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %297 = "llvm.shufflevector"(%270, %296) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %298 = "llvm.sub"(%64, %279) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %299 = "llvm.shufflevector"(%279, %298) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %300 = "llvm.lshr"(%281, %75) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %301 = "llvm.add"(%300, %283) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %302 = "llvm.and"(%281, %76) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %303 = "llvm.lshr"(%289, %75) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %304 = "llvm.add"(%303, %291) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %305 = "llvm.and"(%289, %76) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %306 = "llvm.lshr"(%301, %77) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %307 = "llvm.add"(%306, %285) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %308 = "llvm.and"(%301, %78) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %309 = "llvm.lshr"(%304, %77) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %310 = "llvm.add"(%309, %293) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %311 = "llvm.and"(%304, %78) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %312 = "llvm.lshr"(%307, %75) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %313 = "llvm.add"(%312, %287) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %314 = "llvm.lshr"(%310, %75) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %315 = "llvm.add"(%314, %295) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %316 = "llvm.lshr"(%313, %77) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %317 = "llvm.add"(%316, %305) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %318 = "llvm.lshr"(%315, %77) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %319 = "llvm.add"(%318, %297) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %320 = "llvm.lshr"(%317, %75) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %321 = "llvm.add"(%320, %311) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %322 = "llvm.lshr"(%319, %75) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %323 = "llvm.add"(%322, %299) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %324 = "llvm.lshr"(%323, %77) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %325 = "llvm.and"(%324, %76) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %326 = "llvm.lshr"(%323, %79) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %327 = "llvm.mul"(%325, %41) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %328 = "llvm.mul"(%326, %41) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %329 = "llvm.add"(%327, %302) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %330 = "llvm.add"(%328, %308) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %331 = "llvm.lshr"(%329, %75) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %332 = "llvm.add"(%330, %331) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %333 = "llvm.bitcast"(%329) : (vector<4xi64>) -> vector<8xi32>
    %334 = "llvm.and"(%333, %97) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %335 = "llvm.bitcast"(%332) : (vector<4xi64>) -> vector<8xi32>
    %336 = "llvm.shufflevector"(%334, %335) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %337 = "llvm.bitcast"(%307) : (vector<4xi64>) -> vector<8xi32>
    %338 = "llvm.and"(%337, %97) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %339 = "llvm.bitcast"(%313) : (vector<4xi64>) -> vector<8xi32>
    %340 = "llvm.and"(%339, %115) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %341 = "llvm.shufflevector"(%338, %340) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %342 = "llvm.bitcast"(%321) : (vector<4xi64>) -> vector<8xi32>
    %343 = "llvm.bitcast"(%317) : (vector<4xi64>) -> vector<8xi32>
    %344 = "llvm.and"(%343, %97) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %345 = "llvm.shufflevector"(%344, %342) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %346 = "llvm.bitcast"(%310) : (vector<4xi64>) -> vector<8xi32>
    %347 = "llvm.and"(%346, %97) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %348 = "llvm.bitcast"(%315) : (vector<4xi64>) -> vector<8xi32>
    %349 = "llvm.and"(%348, %115) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %350 = "llvm.shufflevector"(%347, %349) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %351 = "llvm.bitcast"(%319) : (vector<4xi64>) -> vector<8xi32>
    %352 = "llvm.and"(%351, %97) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %353 = "llvm.bitcast"(%323) : (vector<4xi64>) -> vector<8xi32>
    %354 = "llvm.and"(%353, %115) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %355 = "llvm.shufflevector"(%352, %354) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%336, %arg0) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %356 = "llvm.getelementptr"(%arg0, %36) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%341, %356) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %357 = "llvm.getelementptr"(%arg0, %37) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%345, %357) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %358 = "llvm.getelementptr"(%arg0, %38) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%350, %358) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %359 = "llvm.getelementptr"(%arg0, %39) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%355, %359) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

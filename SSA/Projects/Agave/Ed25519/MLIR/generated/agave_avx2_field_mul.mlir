#alias_scope_domain = #llvm.alias_scope_domain<id = distinct[0]<>, description = "_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x48reduce64B1a_NtB2_17___Impl_reduce64__14__impl_reduce64">
#alias_scope = #llvm.alias_scope<id = distinct[1]<>, domain = #alias_scope_domain, description = "_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x48reduce64B1a_NtB2_17___Impl_reduce64__14__impl_reduce64: %_0">
#alias_scope1 = #llvm.alias_scope<id = distinct[2]<>, domain = #alias_scope_domain, description = "_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x48reduce64B1a_NtB2_17___Impl_reduce64__14__impl_reduce64: %z">
"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<fastcc>, arg_attrs = [{llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.writeonly}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], dso_local, function_type = !llvm.func<void (ptr, ptr, ptr)>, inline_hint, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], sym_name = "_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul", target_cpu = "x86-64", target_features = #llvm.target_features<["+avx", "+avx2", "+sse", "+sse2", "+sse3", "+sse4.1", "+sse4.2", "+crc32", "+ssse3"]>, unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 1 : i64, will_return}> ({
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr):
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
    %40 = "llvm.mlir.constant"() <{value = dense<19> : vector<4xi64>}> : () -> vector<4xi64>
    %41 = "llvm.mlir.constant"() <{value = dense<1> : vector<8xi32>}> : () -> vector<8xi32>
    %42 = "llvm.mlir.constant"() <{value = dense<4294967295> : vector<4xi64>}> : () -> vector<4xi64>
    %43 = "llvm.mlir.constant"() <{value = dense<26> : vector<4xi64>}> : () -> vector<4xi64>
    %44 = "llvm.mlir.constant"() <{value = dense<67108863> : vector<4xi64>}> : () -> vector<4xi64>
    %45 = "llvm.mlir.constant"() <{value = dense<25> : vector<4xi64>}> : () -> vector<4xi64>
    %46 = "llvm.mlir.constant"() <{value = dense<33554431> : vector<4xi64>}> : () -> vector<4xi64>
    %47 = "llvm.mlir.constant"() <{value = dense<51> : vector<4xi64>}> : () -> vector<4xi64>
    %48 = "llvm.mlir.constant"() <{value = 67108863 : i32}> : () -> i32
    %49 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %50 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %51 = "llvm.insertelement"(%49, %48, %50) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %52 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %53 = "llvm.insertelement"(%51, %0, %52) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %54 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %55 = "llvm.insertelement"(%53, %48, %54) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %56 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %57 = "llvm.insertelement"(%55, %0, %56) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %58 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %59 = "llvm.insertelement"(%57, %48, %58) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %60 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %61 = "llvm.insertelement"(%59, %0, %60) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %62 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %63 = "llvm.insertelement"(%61, %48, %62) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %64 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %65 = "llvm.insertelement"(%63, %0, %64) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %66 = "llvm.mlir.constant"() <{value = 33554431 : i32}> : () -> i32
    %67 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %68 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %69 = "llvm.insertelement"(%67, %66, %68) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %70 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %71 = "llvm.insertelement"(%69, %0, %70) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %72 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %73 = "llvm.insertelement"(%71, %66, %72) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %74 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %75 = "llvm.insertelement"(%73, %0, %74) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %76 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %77 = "llvm.insertelement"(%75, %66, %76) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %78 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %79 = "llvm.insertelement"(%77, %0, %78) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %80 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %81 = "llvm.insertelement"(%79, %66, %80) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %82 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %83 = "llvm.insertelement"(%81, %0, %82) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %84 = "llvm.load"(%arg1) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %85 = "llvm.shufflevector"(%84, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %86 = "llvm.shufflevector"(%84, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %87 = "llvm.bitcast"(%85) : (vector<8xi32>) -> vector<4xi64>
    %88 = "llvm.bitcast"(%86) : (vector<8xi32>) -> vector<4xi64>
    %89 = "llvm.getelementptr"(%arg1, %36) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %90 = "llvm.load"(%89) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %91 = "llvm.shufflevector"(%90, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %92 = "llvm.shufflevector"(%90, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %93 = "llvm.bitcast"(%91) : (vector<8xi32>) -> vector<4xi64>
    %94 = "llvm.bitcast"(%92) : (vector<8xi32>) -> vector<4xi64>
    %95 = "llvm.getelementptr"(%arg1, %37) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %96 = "llvm.load"(%95) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %97 = "llvm.shufflevector"(%96, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %98 = "llvm.shufflevector"(%96, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %99 = "llvm.bitcast"(%97) : (vector<8xi32>) -> vector<4xi64>
    %100 = "llvm.bitcast"(%98) : (vector<8xi32>) -> vector<4xi64>
    %101 = "llvm.getelementptr"(%arg1, %38) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %102 = "llvm.load"(%101) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %103 = "llvm.shufflevector"(%102, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %104 = "llvm.shufflevector"(%102, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %105 = "llvm.bitcast"(%103) : (vector<8xi32>) -> vector<4xi64>
    %106 = "llvm.bitcast"(%104) : (vector<8xi32>) -> vector<4xi64>
    %107 = "llvm.getelementptr"(%arg1, %39) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %108 = "llvm.load"(%107) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %109 = "llvm.shufflevector"(%108, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %110 = "llvm.shufflevector"(%108, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %111 = "llvm.bitcast"(%109) : (vector<8xi32>) -> vector<4xi64>
    %112 = "llvm.bitcast"(%110) : (vector<8xi32>) -> vector<4xi64>
    %113 = "llvm.load"(%arg2) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %114 = "llvm.shufflevector"(%113, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %115 = "llvm.shufflevector"(%113, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %116 = "llvm.bitcast"(%114) : (vector<8xi32>) -> vector<4xi64>
    %117 = "llvm.bitcast"(%115) : (vector<8xi32>) -> vector<4xi64>
    %118 = "llvm.getelementptr"(%arg2, %36) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %119 = "llvm.load"(%118) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %120 = "llvm.shufflevector"(%119, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %121 = "llvm.shufflevector"(%119, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %122 = "llvm.bitcast"(%120) : (vector<8xi32>) -> vector<4xi64>
    %123 = "llvm.bitcast"(%121) : (vector<8xi32>) -> vector<4xi64>
    %124 = "llvm.getelementptr"(%arg2, %37) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %125 = "llvm.load"(%124) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %126 = "llvm.shufflevector"(%125, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %127 = "llvm.shufflevector"(%125, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %128 = "llvm.bitcast"(%126) : (vector<8xi32>) -> vector<4xi64>
    %129 = "llvm.bitcast"(%127) : (vector<8xi32>) -> vector<4xi64>
    %130 = "llvm.getelementptr"(%arg2, %38) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %131 = "llvm.load"(%130) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %132 = "llvm.shufflevector"(%131, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %133 = "llvm.shufflevector"(%131, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %134 = "llvm.bitcast"(%132) : (vector<8xi32>) -> vector<4xi64>
    %135 = "llvm.bitcast"(%133) : (vector<8xi32>) -> vector<4xi64>
    %136 = "llvm.getelementptr"(%arg2, %39) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %137 = "llvm.load"(%136) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %138 = "llvm.shufflevector"(%137, %18) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %139 = "llvm.shufflevector"(%137, %35) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %140 = "llvm.bitcast"(%138) : (vector<8xi32>) -> vector<4xi64>
    %141 = "llvm.bitcast"(%139) : (vector<8xi32>) -> vector<4xi64>
    %142 = "llvm.mul"(%117, %40) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %143 = "llvm.mul"(%122, %40) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %144 = "llvm.mul"(%123, %40) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %145 = "llvm.mul"(%128, %40) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %146 = "llvm.mul"(%129, %40) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %147 = "llvm.mul"(%134, %40) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %148 = "llvm.mul"(%135, %40) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %149 = "llvm.mul"(%140, %40) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %150 = "llvm.mul"(%141, %40) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %151 = "llvm.mul"(%116, %87) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %152 = "llvm.shl"(%86, %41) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %153 = "llvm.bitcast"(%152) : (vector<8xi32>) -> vector<4xi64>
    %154 = "llvm.and"(%150, %42) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %155 = "llvm.mul"(%154, %153) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %156 = "llvm.and"(%149, %42) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %157 = "llvm.mul"(%156, %93) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %158 = "llvm.shl"(%92, %41) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %159 = "llvm.bitcast"(%158) : (vector<8xi32>) -> vector<4xi64>
    %160 = "llvm.and"(%148, %42) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %161 = "llvm.mul"(%160, %159) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %162 = "llvm.and"(%147, %42) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %163 = "llvm.mul"(%162, %99) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %164 = "llvm.shl"(%98, %41) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %165 = "llvm.bitcast"(%164) : (vector<8xi32>) -> vector<4xi64>
    %166 = "llvm.and"(%146, %42) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %167 = "llvm.mul"(%166, %165) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %168 = "llvm.and"(%145, %42) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %169 = "llvm.mul"(%168, %105) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %170 = "llvm.shl"(%104, %41) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %171 = "llvm.bitcast"(%170) : (vector<8xi32>) -> vector<4xi64>
    %172 = "llvm.and"(%144, %42) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %173 = "llvm.mul"(%172, %171) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %174 = "llvm.and"(%143, %42) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %175 = "llvm.mul"(%174, %111) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %176 = "llvm.shl"(%110, %41) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %177 = "llvm.bitcast"(%176) : (vector<8xi32>) -> vector<4xi64>
    %178 = "llvm.and"(%142, %42) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %179 = "llvm.mul"(%178, %177) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %180 = "llvm.add"(%179, %151) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %181 = "llvm.add"(%180, %175) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %182 = "llvm.add"(%181, %173) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %183 = "llvm.add"(%182, %169) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %184 = "llvm.add"(%183, %167) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %185 = "llvm.add"(%184, %163) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %186 = "llvm.add"(%185, %161) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %187 = "llvm.add"(%186, %157) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %188 = "llvm.add"(%187, %155) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %189 = "llvm.mul"(%117, %87) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %190 = "llvm.mul"(%116, %88) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %191 = "llvm.mul"(%154, %93) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %192 = "llvm.mul"(%156, %94) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %193 = "llvm.mul"(%160, %99) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %194 = "llvm.mul"(%162, %100) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %195 = "llvm.mul"(%166, %105) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %196 = "llvm.mul"(%168, %106) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %197 = "llvm.mul"(%172, %111) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %198 = "llvm.mul"(%174, %112) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %199 = "llvm.mul"(%122, %87) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %200 = "llvm.mul"(%117, %153) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %201 = "llvm.mul"(%116, %93) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %202 = "llvm.mul"(%154, %159) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %203 = "llvm.mul"(%156, %99) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %204 = "llvm.mul"(%160, %165) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %205 = "llvm.mul"(%162, %105) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %206 = "llvm.mul"(%166, %171) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %207 = "llvm.mul"(%168, %111) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %208 = "llvm.mul"(%172, %177) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %209 = "llvm.mul"(%123, %87) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %210 = "llvm.mul"(%122, %88) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %211 = "llvm.mul"(%117, %93) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %212 = "llvm.mul"(%116, %94) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %213 = "llvm.mul"(%154, %99) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %214 = "llvm.mul"(%156, %100) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %215 = "llvm.mul"(%160, %105) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %216 = "llvm.mul"(%162, %106) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %217 = "llvm.mul"(%166, %111) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %218 = "llvm.mul"(%168, %112) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %219 = "llvm.mul"(%128, %87) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %220 = "llvm.mul"(%123, %153) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %221 = "llvm.mul"(%122, %93) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %222 = "llvm.mul"(%117, %159) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %223 = "llvm.mul"(%116, %99) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %224 = "llvm.mul"(%154, %165) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %225 = "llvm.mul"(%156, %105) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %226 = "llvm.mul"(%160, %171) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %227 = "llvm.mul"(%162, %111) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %228 = "llvm.mul"(%166, %177) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %229 = "llvm.add"(%223, %222) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %230 = "llvm.add"(%229, %221) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %231 = "llvm.add"(%230, %220) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %232 = "llvm.add"(%231, %219) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %233 = "llvm.add"(%232, %228) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %234 = "llvm.add"(%233, %227) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %235 = "llvm.add"(%234, %226) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %236 = "llvm.add"(%235, %225) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %237 = "llvm.add"(%236, %224) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %238 = "llvm.mul"(%129, %87) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %239 = "llvm.mul"(%128, %88) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %240 = "llvm.mul"(%123, %93) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %241 = "llvm.mul"(%122, %94) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %242 = "llvm.mul"(%117, %99) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %243 = "llvm.mul"(%116, %100) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %244 = "llvm.mul"(%154, %105) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %245 = "llvm.mul"(%156, %106) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %246 = "llvm.mul"(%160, %111) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %247 = "llvm.mul"(%162, %112) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %248 = "llvm.mul"(%134, %87) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %249 = "llvm.mul"(%129, %153) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %250 = "llvm.mul"(%128, %93) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %251 = "llvm.mul"(%123, %159) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %252 = "llvm.mul"(%122, %99) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %253 = "llvm.mul"(%117, %165) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %254 = "llvm.mul"(%116, %105) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %255 = "llvm.mul"(%154, %171) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %256 = "llvm.mul"(%156, %111) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %257 = "llvm.mul"(%160, %177) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %258 = "llvm.mul"(%135, %87) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %259 = "llvm.mul"(%134, %88) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %260 = "llvm.mul"(%129, %93) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %261 = "llvm.mul"(%128, %94) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %262 = "llvm.mul"(%123, %99) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %263 = "llvm.mul"(%122, %100) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %264 = "llvm.mul"(%117, %105) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %265 = "llvm.mul"(%116, %106) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %266 = "llvm.mul"(%154, %111) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %267 = "llvm.mul"(%156, %112) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %268 = "llvm.mul"(%140, %87) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %269 = "llvm.mul"(%135, %153) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %270 = "llvm.mul"(%134, %93) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %271 = "llvm.mul"(%129, %159) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %272 = "llvm.mul"(%128, %99) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %273 = "llvm.mul"(%123, %165) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %274 = "llvm.mul"(%122, %105) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %275 = "llvm.mul"(%117, %171) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %276 = "llvm.mul"(%116, %111) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %277 = "llvm.mul"(%154, %177) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %278 = "llvm.mul"(%141, %87) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %279 = "llvm.mul"(%140, %88) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %280 = "llvm.mul"(%135, %93) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %281 = "llvm.mul"(%134, %94) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %282 = "llvm.mul"(%129, %99) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %283 = "llvm.mul"(%128, %100) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %284 = "llvm.mul"(%123, %105) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %285 = "llvm.mul"(%122, %106) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %286 = "llvm.mul"(%117, %111) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %287 = "llvm.mul"(%116, %112) <{overflowFlags = 2 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %288 = "llvm.lshr"(%188, %43) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %289 = "llvm.add"(%190, %189) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %290 = "llvm.add"(%289, %197) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %291 = "llvm.add"(%290, %198) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %292 = "llvm.add"(%291, %195) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %293 = "llvm.add"(%292, %196) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %294 = "llvm.add"(%293, %193) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %295 = "llvm.add"(%294, %194) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %296 = "llvm.add"(%295, %191) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %297 = "llvm.add"(%296, %192) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %298 = "llvm.add"(%297, %288) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %299 = "llvm.and"(%188, %44) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %300 = "llvm.lshr"(%237, %43) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %301 = "llvm.add"(%243, %242) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %302 = "llvm.add"(%301, %240) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %303 = "llvm.add"(%302, %241) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %304 = "llvm.add"(%303, %238) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %305 = "llvm.add"(%304, %239) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %306 = "llvm.add"(%305, %246) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %307 = "llvm.add"(%306, %247) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %308 = "llvm.add"(%307, %244) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %309 = "llvm.add"(%308, %245) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %310 = "llvm.add"(%309, %300) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %311 = "llvm.and"(%237, %44) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %312 = "llvm.lshr"(%298, %45) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %313 = "llvm.add"(%201, %200) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %314 = "llvm.add"(%313, %199) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %315 = "llvm.add"(%314, %208) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %316 = "llvm.add"(%315, %207) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %317 = "llvm.add"(%316, %206) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %318 = "llvm.add"(%317, %205) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %319 = "llvm.add"(%318, %204) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %320 = "llvm.add"(%319, %203) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %321 = "llvm.add"(%320, %202) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %322 = "llvm.add"(%321, %312) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %323 = "llvm.and"(%298, %46) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %324 = "llvm.lshr"(%310, %45) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %325 = "llvm.add"(%254, %253) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %326 = "llvm.add"(%325, %251) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %327 = "llvm.add"(%326, %252) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %328 = "llvm.add"(%327, %250) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %329 = "llvm.add"(%328, %249) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %330 = "llvm.add"(%329, %248) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %331 = "llvm.add"(%330, %257) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %332 = "llvm.add"(%331, %256) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %333 = "llvm.add"(%332, %255) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %334 = "llvm.add"(%333, %324) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %335 = "llvm.and"(%310, %46) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %336 = "llvm.lshr"(%322, %43) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %337 = "llvm.add"(%212, %211) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %338 = "llvm.add"(%337, %209) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %339 = "llvm.add"(%338, %210) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %340 = "llvm.add"(%339, %217) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %341 = "llvm.add"(%340, %218) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %342 = "llvm.add"(%341, %215) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %343 = "llvm.add"(%342, %216) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %344 = "llvm.add"(%343, %213) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %345 = "llvm.add"(%344, %214) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %346 = "llvm.add"(%345, %336) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %347 = "llvm.lshr"(%334, %43) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %348 = "llvm.add"(%265, %264) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %349 = "llvm.add"(%348, %262) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %350 = "llvm.add"(%349, %263) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %351 = "llvm.add"(%350, %260) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %352 = "llvm.add"(%351, %261) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %353 = "llvm.add"(%352, %258) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %354 = "llvm.add"(%353, %259) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %355 = "llvm.add"(%354, %266) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %356 = "llvm.add"(%355, %267) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %357 = "llvm.add"(%356, %347) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %358 = "llvm.lshr"(%346, %45) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %359 = "llvm.add"(%358, %311) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %360 = "llvm.lshr"(%357, %45) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %361 = "llvm.add"(%275, %276) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %362 = "llvm.add"(%361, %274) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %363 = "llvm.add"(%362, %273) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %364 = "llvm.add"(%363, %272) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %365 = "llvm.add"(%364, %271) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %366 = "llvm.add"(%365, %270) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %367 = "llvm.add"(%366, %269) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %368 = "llvm.add"(%367, %268) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %369 = "llvm.add"(%368, %277) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %370 = "llvm.add"(%369, %360) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %371 = "llvm.lshr"(%359, %43) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %372 = "llvm.add"(%371, %335) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %373 = "llvm.lshr"(%370, %43) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %374 = "llvm.add"(%287, %286) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %375 = "llvm.add"(%374, %284) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %376 = "llvm.add"(%375, %285) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %377 = "llvm.add"(%376, %282) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %378 = "llvm.add"(%377, %283) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %379 = "llvm.add"(%378, %280) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %380 = "llvm.add"(%379, %281) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %381 = "llvm.add"(%380, %278) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %382 = "llvm.add"(%381, %279) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %383 = "llvm.add"(%382, %373) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %384 = "llvm.lshr"(%383, %45) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %385 = "llvm.and"(%384, %44) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %386 = "llvm.lshr"(%383, %47) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %387 = "llvm.mul"(%385, %40) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %388 = "llvm.mul"(%386, %40) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %389 = "llvm.add"(%387, %299) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %390 = "llvm.add"(%388, %323) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %391 = "llvm.lshr"(%389, %43) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %392 = "llvm.add"(%390, %391) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %393 = "llvm.bitcast"(%389) : (vector<4xi64>) -> vector<8xi32>
    %394 = "llvm.and"(%393, %65) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %395 = "llvm.bitcast"(%392) : (vector<4xi64>) -> vector<8xi32>
    %396 = "llvm.shufflevector"(%394, %395) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %397 = "llvm.bitcast"(%322) : (vector<4xi64>) -> vector<8xi32>
    %398 = "llvm.and"(%397, %65) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %399 = "llvm.bitcast"(%346) : (vector<4xi64>) -> vector<8xi32>
    %400 = "llvm.and"(%399, %83) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %401 = "llvm.shufflevector"(%398, %400) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %402 = "llvm.bitcast"(%372) : (vector<4xi64>) -> vector<8xi32>
    %403 = "llvm.bitcast"(%359) : (vector<4xi64>) -> vector<8xi32>
    %404 = "llvm.and"(%403, %65) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %405 = "llvm.shufflevector"(%404, %402) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %406 = "llvm.bitcast"(%334) : (vector<4xi64>) -> vector<8xi32>
    %407 = "llvm.and"(%406, %65) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %408 = "llvm.bitcast"(%357) : (vector<4xi64>) -> vector<8xi32>
    %409 = "llvm.and"(%408, %83) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %410 = "llvm.shufflevector"(%407, %409) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %411 = "llvm.bitcast"(%370) : (vector<4xi64>) -> vector<8xi32>
    %412 = "llvm.and"(%411, %65) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %413 = "llvm.bitcast"(%383) : (vector<4xi64>) -> vector<8xi32>
    %414 = "llvm.and"(%413, %83) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %415 = "llvm.shufflevector"(%412, %414) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%396, %arg0) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %416 = "llvm.getelementptr"(%arg0, %36) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%401, %416) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %417 = "llvm.getelementptr"(%arg0, %37) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%405, %417) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %418 = "llvm.getelementptr"(%arg0, %38) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%410, %418) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %419 = "llvm.getelementptr"(%arg0, %39) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%415, %419) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

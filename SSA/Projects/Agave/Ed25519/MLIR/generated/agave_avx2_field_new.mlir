#alias_scope_domain = #llvm.alias_scope_domain<id = distinct[0]<>, description = "_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x46reduceB1a_NtB2_15___Impl_reduce__12__impl_reduce">
#alias_scope = #llvm.alias_scope<id = distinct[1]<>, domain = #alias_scope_domain, description = "_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x46reduceB1a_NtB2_15___Impl_reduce__12__impl_reduce: %_0">
#alias_scope1 = #llvm.alias_scope<id = distinct[2]<>, domain = #alias_scope_domain, description = "_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x46reduceB1a_NtB2_15___Impl_reduce__12__impl_reduce: %self">
"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.noundef, llvm.sret = !llvm.array<160 x i8>, llvm.writeonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.noundef, llvm.readonly}], function_type = !llvm.func<void (ptr, ptr, ptr, ptr, ptr)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], sym_name = "_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x43newB1a_NtB2_12___Impl_new__9__impl_new", target_cpu = "x86-64", target_features = #llvm.target_features<["+avx", "+avx2", "+sse", "+sse2", "+sse3", "+sse4.1", "+sse4.2", "+crc32", "+ssse3"]>, unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr, %arg3: !llvm.ptr, %arg4: !llvm.ptr):
    %0 = "llvm.mlir.poison"() : () -> vector<4xi32>
    %1 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = dense<67108863> : vector<4xi32>}> : () -> vector<4xi32>
    %6 = "llvm.mlir.poison"() : () -> vector<4xi64>
    %7 = "llvm.mlir.constant"() <{value = dense<26> : vector<4xi64>}> : () -> vector<4xi64>
    %8 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = dense<[26, 26, 25, 25, 26, 26, 25, 25]> : vector<8xi32>}> : () -> vector<8xi32>
    %13 = "llvm.mlir.constant"() <{value = dense<[67108863, 67108863, 33554431, 33554431, 67108863, 67108863, 33554431, 33554431]> : vector<8xi32>}> : () -> vector<8xi32>
    %14 = "llvm.mlir.constant"() <{value = dense<[0, 0, 127, 127, 0, 0, 127, 127]> : vector<8xi32>}> : () -> vector<8xi32>
    %15 = "llvm.mlir.poison"() : () -> vector<8xi32>
    %16 = "llvm.mlir.constant"() <{value = dense<19> : vector<4xi64>}> : () -> vector<4xi64>
    %17 = "llvm.mlir.constant"() <{value = 64 : i64}> : () -> i64
    %18 = "llvm.mlir.constant"() <{value = 96 : i64}> : () -> i64
    %19 = "llvm.mlir.constant"() <{value = 128 : i64}> : () -> i64
    %20 = "llvm.load"(%arg1) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %21 = "llvm.load"(%arg2) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %22 = "llvm.load"(%arg3) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %23 = "llvm.load"(%arg4) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %24 = "llvm.trunc"(%23) <{overflowFlags = 0 : i32}> : (i64) -> i32
    %25 = "llvm.trunc"(%22) <{overflowFlags = 0 : i32}> : (i64) -> i32
    %26 = "llvm.trunc"(%21) <{overflowFlags = 0 : i32}> : (i64) -> i32
    %27 = "llvm.trunc"(%20) <{overflowFlags = 0 : i32}> : (i64) -> i32
    %28 = "llvm.insertelement"(%0, %27, %1) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %29 = "llvm.insertelement"(%28, %26, %2) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %30 = "llvm.insertelement"(%29, %25, %3) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %31 = "llvm.insertelement"(%30, %24, %4) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %32 = "llvm.and"(%31, %5) : (vector<4xi32>, vector<4xi32>) -> vector<4xi32>
    %33 = "llvm.insertelement"(%6, %20, %1) : (vector<4xi64>, i64, i64) -> vector<4xi64>
    %34 = "llvm.insertelement"(%33, %21, %2) : (vector<4xi64>, i64, i64) -> vector<4xi64>
    %35 = "llvm.insertelement"(%34, %22, %3) : (vector<4xi64>, i64, i64) -> vector<4xi64>
    %36 = "llvm.insertelement"(%35, %23, %4) : (vector<4xi64>, i64, i64) -> vector<4xi64>
    %37 = "llvm.lshr"(%36, %7) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %38 = "llvm.trunc"(%37) <{overflowFlags = 0 : i32}> : (vector<4xi64>) -> vector<4xi32>
    %39 = "llvm.shufflevector"(%32, %38) <{mask = array<i32: 0, 1, 4, 5, 2, 3, 6, 7>}> : (vector<4xi32>, vector<4xi32>) -> vector<8xi32>
    %40 = "llvm.getelementptr"(%arg1, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %41 = "llvm.load"(%40) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %42 = "llvm.getelementptr"(%arg2, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %43 = "llvm.load"(%42) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %44 = "llvm.getelementptr"(%arg3, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %45 = "llvm.load"(%44) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %46 = "llvm.getelementptr"(%arg4, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %47 = "llvm.load"(%46) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %48 = "llvm.trunc"(%47) <{overflowFlags = 0 : i32}> : (i64) -> i32
    %49 = "llvm.trunc"(%45) <{overflowFlags = 0 : i32}> : (i64) -> i32
    %50 = "llvm.trunc"(%43) <{overflowFlags = 0 : i32}> : (i64) -> i32
    %51 = "llvm.trunc"(%41) <{overflowFlags = 0 : i32}> : (i64) -> i32
    %52 = "llvm.insertelement"(%0, %51, %1) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %53 = "llvm.insertelement"(%52, %50, %2) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %54 = "llvm.insertelement"(%53, %49, %3) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %55 = "llvm.insertelement"(%54, %48, %4) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %56 = "llvm.and"(%55, %5) : (vector<4xi32>, vector<4xi32>) -> vector<4xi32>
    %57 = "llvm.insertelement"(%6, %41, %1) : (vector<4xi64>, i64, i64) -> vector<4xi64>
    %58 = "llvm.insertelement"(%57, %43, %2) : (vector<4xi64>, i64, i64) -> vector<4xi64>
    %59 = "llvm.insertelement"(%58, %45, %3) : (vector<4xi64>, i64, i64) -> vector<4xi64>
    %60 = "llvm.insertelement"(%59, %47, %4) : (vector<4xi64>, i64, i64) -> vector<4xi64>
    %61 = "llvm.lshr"(%60, %7) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %62 = "llvm.trunc"(%61) <{overflowFlags = 0 : i32}> : (vector<4xi64>) -> vector<4xi32>
    %63 = "llvm.shufflevector"(%56, %62) <{mask = array<i32: 0, 1, 4, 5, 2, 3, 6, 7>}> : (vector<4xi32>, vector<4xi32>) -> vector<8xi32>
    %64 = "llvm.getelementptr"(%arg1, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %65 = "llvm.load"(%64) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %66 = "llvm.getelementptr"(%arg2, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %67 = "llvm.load"(%66) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %68 = "llvm.getelementptr"(%arg3, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %69 = "llvm.load"(%68) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %70 = "llvm.getelementptr"(%arg4, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %71 = "llvm.load"(%70) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %72 = "llvm.trunc"(%71) <{overflowFlags = 0 : i32}> : (i64) -> i32
    %73 = "llvm.trunc"(%69) <{overflowFlags = 0 : i32}> : (i64) -> i32
    %74 = "llvm.trunc"(%67) <{overflowFlags = 0 : i32}> : (i64) -> i32
    %75 = "llvm.trunc"(%65) <{overflowFlags = 0 : i32}> : (i64) -> i32
    %76 = "llvm.insertelement"(%0, %75, %1) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %77 = "llvm.insertelement"(%76, %74, %2) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %78 = "llvm.insertelement"(%77, %73, %3) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %79 = "llvm.insertelement"(%78, %72, %4) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %80 = "llvm.and"(%79, %5) : (vector<4xi32>, vector<4xi32>) -> vector<4xi32>
    %81 = "llvm.insertelement"(%6, %65, %1) : (vector<4xi64>, i64, i64) -> vector<4xi64>
    %82 = "llvm.insertelement"(%81, %67, %2) : (vector<4xi64>, i64, i64) -> vector<4xi64>
    %83 = "llvm.insertelement"(%82, %69, %3) : (vector<4xi64>, i64, i64) -> vector<4xi64>
    %84 = "llvm.insertelement"(%83, %71, %4) : (vector<4xi64>, i64, i64) -> vector<4xi64>
    %85 = "llvm.lshr"(%84, %7) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %86 = "llvm.trunc"(%85) <{overflowFlags = 0 : i32}> : (vector<4xi64>) -> vector<4xi32>
    %87 = "llvm.shufflevector"(%80, %86) <{mask = array<i32: 0, 1, 4, 5, 2, 3, 6, 7>}> : (vector<4xi32>, vector<4xi32>) -> vector<8xi32>
    %88 = "llvm.getelementptr"(%arg1, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %89 = "llvm.load"(%88) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %90 = "llvm.getelementptr"(%arg2, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %91 = "llvm.load"(%90) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %92 = "llvm.getelementptr"(%arg3, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %93 = "llvm.load"(%92) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %94 = "llvm.getelementptr"(%arg4, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %95 = "llvm.load"(%94) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %96 = "llvm.trunc"(%95) <{overflowFlags = 0 : i32}> : (i64) -> i32
    %97 = "llvm.trunc"(%93) <{overflowFlags = 0 : i32}> : (i64) -> i32
    %98 = "llvm.trunc"(%91) <{overflowFlags = 0 : i32}> : (i64) -> i32
    %99 = "llvm.trunc"(%89) <{overflowFlags = 0 : i32}> : (i64) -> i32
    %100 = "llvm.insertelement"(%0, %99, %1) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %101 = "llvm.insertelement"(%100, %98, %2) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %102 = "llvm.insertelement"(%101, %97, %3) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %103 = "llvm.insertelement"(%102, %96, %4) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %104 = "llvm.and"(%103, %5) : (vector<4xi32>, vector<4xi32>) -> vector<4xi32>
    %105 = "llvm.insertelement"(%6, %89, %1) : (vector<4xi64>, i64, i64) -> vector<4xi64>
    %106 = "llvm.insertelement"(%105, %91, %2) : (vector<4xi64>, i64, i64) -> vector<4xi64>
    %107 = "llvm.insertelement"(%106, %93, %3) : (vector<4xi64>, i64, i64) -> vector<4xi64>
    %108 = "llvm.insertelement"(%107, %95, %4) : (vector<4xi64>, i64, i64) -> vector<4xi64>
    %109 = "llvm.lshr"(%108, %7) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %110 = "llvm.trunc"(%109) <{overflowFlags = 0 : i32}> : (vector<4xi64>) -> vector<4xi32>
    %111 = "llvm.shufflevector"(%104, %110) <{mask = array<i32: 0, 1, 4, 5, 2, 3, 6, 7>}> : (vector<4xi32>, vector<4xi32>) -> vector<8xi32>
    %112 = "llvm.getelementptr"(%arg1, %11) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %113 = "llvm.load"(%112) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %114 = "llvm.getelementptr"(%arg2, %11) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %115 = "llvm.load"(%114) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %116 = "llvm.getelementptr"(%arg3, %11) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %117 = "llvm.load"(%116) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %118 = "llvm.getelementptr"(%arg4, %11) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %119 = "llvm.load"(%118) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %120 = "llvm.trunc"(%119) <{overflowFlags = 0 : i32}> : (i64) -> i32
    %121 = "llvm.trunc"(%117) <{overflowFlags = 0 : i32}> : (i64) -> i32
    %122 = "llvm.trunc"(%115) <{overflowFlags = 0 : i32}> : (i64) -> i32
    %123 = "llvm.trunc"(%113) <{overflowFlags = 0 : i32}> : (i64) -> i32
    %124 = "llvm.insertelement"(%0, %123, %1) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %125 = "llvm.insertelement"(%124, %122, %2) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %126 = "llvm.insertelement"(%125, %121, %3) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %127 = "llvm.insertelement"(%126, %120, %4) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %128 = "llvm.and"(%127, %5) : (vector<4xi32>, vector<4xi32>) -> vector<4xi32>
    %129 = "llvm.insertelement"(%6, %113, %1) : (vector<4xi64>, i64, i64) -> vector<4xi64>
    %130 = "llvm.insertelement"(%129, %115, %2) : (vector<4xi64>, i64, i64) -> vector<4xi64>
    %131 = "llvm.insertelement"(%130, %117, %3) : (vector<4xi64>, i64, i64) -> vector<4xi64>
    %132 = "llvm.insertelement"(%131, %119, %4) : (vector<4xi64>, i64, i64) -> vector<4xi64>
    %133 = "llvm.lshr"(%132, %7) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %134 = "llvm.trunc"(%133) <{overflowFlags = 0 : i32}> : (vector<4xi64>) -> vector<4xi32>
    %135 = "llvm.shufflevector"(%128, %134) <{mask = array<i32: 0, 1, 4, 5, 2, 3, 6, 7>}> : (vector<4xi32>, vector<4xi32>) -> vector<8xi32>
    %136 = "llvm.lshr"(%39, %12) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %137 = "llvm.and"(%39, %13) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %138 = "llvm.lshr"(%63, %12) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %139 = "llvm.shufflevector"(%136, %138) <{mask = array<i32: 2, 3, 8, 9, 6, 7, 12, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %140 = "llvm.and"(%63, %13) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %141 = "llvm.add"(%139, %140) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %142 = "llvm.lshr"(%87, %12) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %143 = "llvm.shufflevector"(%138, %142) <{mask = array<i32: 2, 3, 8, 9, 6, 7, 12, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %144 = "llvm.and"(%87, %13) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %145 = "llvm.add"(%143, %144) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %146 = "llvm.lshr"(%111, %12) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %147 = "llvm.shufflevector"(%142, %146) <{mask = array<i32: 2, 3, 8, 9, 6, 7, 12, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %148 = "llvm.and"(%111, %13) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %149 = "llvm.add"(%147, %148) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %150 = "llvm.lshr"(%135, %12) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %151 = "llvm.shufflevector"(%146, %150) <{mask = array<i32: 2, 3, 8, 9, 6, 7, 12, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %152 = "llvm.and"(%135, %13) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %153 = "llvm.add"(%151, %152) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %154 = "llvm.and"(%150, %14) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %155 = "llvm.shufflevector"(%154, %15) <{mask = array<i32: 2, 0, 3, 1, 6, 4, 7, 5>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %156 = "llvm.bitcast"(%155) : (vector<8xi32>) -> vector<4xi64>
    %157 = "llvm.mul"(%156, %16) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %158 = "llvm.bitcast"(%157) : (vector<4xi64>) -> vector<8xi32>
    %159 = "llvm.shufflevector"(%158, %15) <{mask = array<i32: 0, 2, 1, 3, 4, 6, 5, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %160 = "llvm.add"(%137, %159) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%160, %arg0) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %161 = "llvm.getelementptr"(%arg0, %11) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%141, %161) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %162 = "llvm.getelementptr"(%arg0, %17) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%145, %162) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %163 = "llvm.getelementptr"(%arg0, %18) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%149, %163) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %164 = "llvm.getelementptr"(%arg0, %19) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%153, %164) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

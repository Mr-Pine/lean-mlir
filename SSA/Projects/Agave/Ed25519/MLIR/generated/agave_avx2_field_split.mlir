"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.noundef, llvm.sret = !llvm.array<160 x i8>, llvm.writeonly}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.noundef, llvm.readonly}], function_type = !llvm.func<void (ptr, ptr)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], sym_name = "_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x45splitB1a_NtB2_14___Impl_split__11__impl_split", target_cpu = "x86-64", target_features = #llvm.target_features<["+avx", "+avx2", "+sse", "+sse2", "+sse3", "+sse4.1", "+sse4.2", "+crc32", "+ssse3"]>, unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 36 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 44 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 48 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 52 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 56 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 60 : i64}> : () -> i64
    %8 = "llvm.mlir.poison"() : () -> vector<8xi32>
    %9 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = dense<26> : vector<2xi64>}> : () -> vector<2xi64>
    %11 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 128 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 64 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = 68 : i64}> : () -> i64
    %15 = "llvm.mlir.constant"() <{value = 72 : i64}> : () -> i64
    %16 = "llvm.mlir.constant"() <{value = 76 : i64}> : () -> i64
    %17 = "llvm.mlir.constant"() <{value = 80 : i64}> : () -> i64
    %18 = "llvm.mlir.constant"() <{value = 84 : i64}> : () -> i64
    %19 = "llvm.mlir.constant"() <{value = 88 : i64}> : () -> i64
    %20 = "llvm.mlir.constant"() <{value = 92 : i64}> : () -> i64
    %21 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %22 = "llvm.mlir.constant"() <{value = 96 : i64}> : () -> i64
    %23 = "llvm.mlir.constant"() <{value = 136 : i64}> : () -> i64
    %24 = "llvm.mlir.constant"() <{value = 100 : i64}> : () -> i64
    %25 = "llvm.mlir.constant"() <{value = 104 : i64}> : () -> i64
    %26 = "llvm.mlir.constant"() <{value = 108 : i64}> : () -> i64
    %27 = "llvm.mlir.constant"() <{value = 112 : i64}> : () -> i64
    %28 = "llvm.mlir.constant"() <{value = 116 : i64}> : () -> i64
    %29 = "llvm.mlir.constant"() <{value = 120 : i64}> : () -> i64
    %30 = "llvm.mlir.constant"() <{value = 124 : i64}> : () -> i64
    %31 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> i64
    %32 = "llvm.mlir.constant"() <{value = 144 : i64}> : () -> i64
    %33 = "llvm.mlir.constant"() <{value = 132 : i64}> : () -> i64
    %34 = "llvm.mlir.constant"() <{value = 140 : i64}> : () -> i64
    %35 = "llvm.mlir.constant"() <{value = 148 : i64}> : () -> i64
    %36 = "llvm.mlir.constant"() <{value = 152 : i64}> : () -> i64
    %37 = "llvm.mlir.constant"() <{value = 156 : i64}> : () -> i64
    %38 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %39 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %40 = "llvm.mlir.constant"() <{value = dense<26> : vector<4xi64>}> : () -> vector<4xi64>
    %41 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %42 = "llvm.load"(%arg1) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %43 = "llvm.getelementptr"(%arg1, %0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %44 = "llvm.load"(%43) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %45 = "llvm.getelementptr"(%arg1, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %46 = "llvm.load"(%45) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %47 = "llvm.zext"(%46) : (i32) -> i64
    %48 = "llvm.getelementptr"(%arg1, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %49 = "llvm.load"(%48) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %50 = "llvm.getelementptr"(%arg1, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %51 = "llvm.load"(%50) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %52 = "llvm.zext"(%51) : (i32) -> i64
    %53 = "llvm.getelementptr"(%arg1, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %54 = "llvm.load"(%53) <{alignment = 16 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %55 = "llvm.getelementptr"(%arg1, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %56 = "llvm.load"(%55) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %57 = "llvm.zext"(%56) : (i32) -> i64
    %58 = "llvm.getelementptr"(%arg1, %6) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %59 = "llvm.load"(%58) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %60 = "llvm.getelementptr"(%arg1, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %61 = "llvm.load"(%60) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %62 = "llvm.zext"(%61) : (i32) -> i64
    %63 = "llvm.shufflevector"(%42, %8) <{mask = array<i32: 0, 1>}> : (vector<8xi32>, vector<8xi32>) -> vector<2xi32>
    %64 = "llvm.insertelement"(%63, %44, %9) : (vector<2xi32>, i32, i64) -> vector<2xi32>
    %65 = "llvm.zext"(%64) : (vector<2xi32>) -> vector<2xi64>
    %66 = "llvm.shufflevector"(%42, %8) <{mask = array<i32: 2, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<2xi32>
    %67 = "llvm.insertelement"(%66, %49, %9) : (vector<2xi32>, i32, i64) -> vector<2xi32>
    %68 = "llvm.zext"(%67) : (vector<2xi32>) -> vector<2xi64>
    %69 = "llvm.shl"(%68, %10) <{overflowFlags = 3 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %70 = "llvm.add"(%69, %65) <{overflowFlags = 3 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    "llvm.store"(%70, %arg0) <{alignment = 8 : i64, ordering = 0 : i64}> : (vector<2xi64>, !llvm.ptr) -> ()
    %71 = "llvm.shl"(%52, %11) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %72 = "llvm.getelementptr"(%arg0, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %73 = "llvm.add"(%71, %47) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.store"(%73, %72) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %74 = "llvm.shl"(%62, %11) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %75 = "llvm.getelementptr"(%arg0, %12) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %76 = "llvm.add"(%74, %57) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.store"(%76, %75) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %77 = "llvm.getelementptr"(%arg1, %13) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %78 = "llvm.load"(%77) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %79 = "llvm.zext"(%78) : (i32) -> i64
    %80 = "llvm.getelementptr"(%arg1, %14) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %81 = "llvm.load"(%80) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %82 = "llvm.zext"(%81) : (i32) -> i64
    %83 = "llvm.getelementptr"(%arg1, %15) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %84 = "llvm.load"(%83) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %85 = "llvm.zext"(%84) : (i32) -> i64
    %86 = "llvm.getelementptr"(%arg1, %16) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %87 = "llvm.load"(%86) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %88 = "llvm.zext"(%87) : (i32) -> i64
    %89 = "llvm.getelementptr"(%arg1, %17) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %90 = "llvm.load"(%89) <{alignment = 16 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %91 = "llvm.getelementptr"(%arg1, %18) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %92 = "llvm.load"(%91) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %93 = "llvm.zext"(%92) : (i32) -> i64
    %94 = "llvm.getelementptr"(%arg1, %19) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %95 = "llvm.load"(%94) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %96 = "llvm.getelementptr"(%arg1, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %97 = "llvm.load"(%96) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %98 = "llvm.zext"(%97) : (i32) -> i64
    %99 = "llvm.shl"(%85, %11) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %100 = "llvm.getelementptr"(%arg0, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %101 = "llvm.add"(%99, %79) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.store"(%101, %100) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %102 = "llvm.shl"(%88, %11) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %103 = "llvm.getelementptr"(%arg0, %6) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %104 = "llvm.add"(%102, %82) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.store"(%104, %103) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %105 = "llvm.getelementptr"(%arg0, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %106 = "llvm.shl"(%98, %11) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %107 = "llvm.getelementptr"(%arg0, %23) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %108 = "llvm.add"(%106, %93) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.store"(%108, %107) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %109 = "llvm.getelementptr"(%arg1, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %110 = "llvm.load"(%109) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %111 = "llvm.zext"(%110) : (i32) -> i64
    %112 = "llvm.getelementptr"(%arg1, %24) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %113 = "llvm.load"(%112) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %114 = "llvm.getelementptr"(%arg1, %25) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %115 = "llvm.load"(%114) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %116 = "llvm.zext"(%115) : (i32) -> i64
    %117 = "llvm.getelementptr"(%arg1, %26) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %118 = "llvm.load"(%117) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %119 = "llvm.getelementptr"(%arg1, %27) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %120 = "llvm.load"(%119) <{alignment = 16 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %121 = "llvm.getelementptr"(%arg1, %28) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %122 = "llvm.load"(%121) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %123 = "llvm.zext"(%122) : (i32) -> i64
    %124 = "llvm.getelementptr"(%arg1, %29) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %125 = "llvm.load"(%124) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %126 = "llvm.getelementptr"(%arg1, %30) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %127 = "llvm.load"(%126) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %128 = "llvm.zext"(%127) : (i32) -> i64
    %129 = "llvm.shl"(%116, %11) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %130 = "llvm.getelementptr"(%arg0, %31) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %131 = "llvm.add"(%129, %111) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.store"(%131, %130) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %132 = "llvm.getelementptr"(%arg0, %13) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %133 = "llvm.shl"(%128, %11) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %134 = "llvm.getelementptr"(%arg0, %32) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %135 = "llvm.add"(%133, %123) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.store"(%135, %134) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %136 = "llvm.getelementptr"(%arg1, %12) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %137 = "llvm.load"(%136) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %138 = "llvm.getelementptr"(%arg1, %33) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %139 = "llvm.load"(%138) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %140 = "llvm.getelementptr"(%arg1, %23) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %141 = "llvm.load"(%140) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %142 = "llvm.getelementptr"(%arg1, %34) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %143 = "llvm.load"(%142) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %144 = "llvm.getelementptr"(%arg1, %32) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %145 = "llvm.load"(%144) <{alignment = 16 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %146 = "llvm.getelementptr"(%arg1, %35) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %147 = "llvm.load"(%146) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %148 = "llvm.zext"(%147) : (i32) -> i64
    %149 = "llvm.getelementptr"(%arg1, %36) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %150 = "llvm.load"(%149) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %151 = "llvm.getelementptr"(%arg1, %37) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %152 = "llvm.load"(%151) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %153 = "llvm.zext"(%152) : (i32) -> i64
    %154 = "llvm.getelementptr"(%arg0, %0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %155 = "llvm.insertelement"(%63, %137, %38) : (vector<2xi32>, i32, i64) -> vector<2xi32>
    %156 = "llvm.zext"(%155) : (vector<2xi32>) -> vector<2xi64>
    %157 = "llvm.insertelement"(%66, %141, %38) : (vector<2xi32>, i32, i64) -> vector<2xi32>
    %158 = "llvm.zext"(%157) : (vector<2xi32>) -> vector<2xi64>
    %159 = "llvm.shl"(%158, %10) <{overflowFlags = 3 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %160 = "llvm.add"(%159, %156) <{overflowFlags = 3 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    "llvm.store"(%160, %154) <{alignment = 8 : i64, ordering = 0 : i64}> : (vector<2xi64>, !llvm.ptr) -> ()
    %161 = "llvm.shufflevector"(%42, %8) <{mask = array<i32: -1, -1, 4, 5>}> : (vector<8xi32>, vector<8xi32>) -> vector<4xi32>
    %162 = "llvm.insertelement"(%161, %113, %38) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %163 = "llvm.insertelement"(%162, %139, %9) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %164 = "llvm.insertelement"(%163, %54, %39) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %165 = "llvm.zext"(%164) : (vector<4xi32>) -> vector<4xi64>
    %166 = "llvm.shufflevector"(%42, %8) <{mask = array<i32: -1, -1, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<4xi32>
    %167 = "llvm.insertelement"(%166, %118, %38) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %168 = "llvm.insertelement"(%167, %143, %9) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %169 = "llvm.insertelement"(%168, %59, %39) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %170 = "llvm.zext"(%169) : (vector<4xi32>) -> vector<4xi64>
    %171 = "llvm.shl"(%170, %40) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %172 = "llvm.add"(%171, %165) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    "llvm.store"(%172, %132) <{alignment = 8 : i64, ordering = 0 : i64}> : (vector<4xi64>, !llvm.ptr) -> ()
    %173 = "llvm.insertelement"(%161, %90, %38) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %174 = "llvm.insertelement"(%173, %120, %9) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %175 = "llvm.insertelement"(%174, %145, %41) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %176 = "llvm.zext"(%175) : (vector<4xi32>) -> vector<4xi64>
    %177 = "llvm.insertelement"(%166, %95, %38) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %178 = "llvm.insertelement"(%177, %125, %9) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %179 = "llvm.insertelement"(%178, %150, %41) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %180 = "llvm.zext"(%179) : (vector<4xi32>) -> vector<4xi64>
    %181 = "llvm.shl"(%180, %40) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %182 = "llvm.add"(%181, %176) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    "llvm.store"(%182, %105) <{alignment = 8 : i64, ordering = 0 : i64}> : (vector<4xi64>, !llvm.ptr) -> ()
    %183 = "llvm.shl"(%153, %11) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %184 = "llvm.getelementptr"(%arg0, %36) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %185 = "llvm.add"(%183, %148) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.store"(%185, %184) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

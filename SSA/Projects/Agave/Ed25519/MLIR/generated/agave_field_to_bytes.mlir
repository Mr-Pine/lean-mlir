"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.align = 1 : i64, llvm.dereferenceable = 32 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.noundef, llvm.sret = !llvm.array<32 x i8>, llvm.writeonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.noundef, llvm.readonly}], function_type = !llvm.func<void (ptr, ptr)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], sym_name = "_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement518to_bytes", target_cpu = "x86-64", unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 48 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %15 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %16 = "llvm.mlir.constant"() <{value = 13 : i64}> : () -> i64
    %17 = "llvm.mlir.constant"() <{value = 21 : i64}> : () -> i64
    %18 = "llvm.mlir.constant"() <{value = 9 : i64}> : () -> i64
    %19 = "llvm.mlir.constant"() <{value = 29 : i64}> : () -> i64
    %20 = "llvm.mlir.constant"() <{value = 10 : i64}> : () -> i64
    %21 = "llvm.mlir.constant"() <{value = 37 : i64}> : () -> i64
    %22 = "llvm.mlir.constant"() <{value = 11 : i64}> : () -> i64
    %23 = "llvm.mlir.constant"() <{value = 45 : i64}> : () -> i64
    %24 = "llvm.mlir.constant"() <{value = 12 : i64}> : () -> i64
    %25 = "llvm.mlir.constant"() <{value = 14 : i64}> : () -> i64
    %26 = "llvm.mlir.constant"() <{value = 18 : i64}> : () -> i64
    %27 = "llvm.mlir.constant"() <{value = 15 : i64}> : () -> i64
    %28 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %29 = "llvm.mlir.constant"() <{value = 34 : i64}> : () -> i64
    %30 = "llvm.mlir.constant"() <{value = 17 : i64}> : () -> i64
    %31 = "llvm.mlir.constant"() <{value = 42 : i64}> : () -> i64
    %32 = "llvm.mlir.constant"() <{value = 50 : i64}> : () -> i64
    %33 = "llvm.mlir.constant"() <{value = 20 : i64}> : () -> i64
    %34 = "llvm.mlir.constant"() <{value = 23 : i64}> : () -> i64
    %35 = "llvm.mlir.constant"() <{value = 22 : i64}> : () -> i64
    %36 = "llvm.mlir.constant"() <{value = 31 : i64}> : () -> i64
    %37 = "llvm.mlir.constant"() <{value = 39 : i64}> : () -> i64
    %38 = "llvm.mlir.constant"() <{value = 47 : i64}> : () -> i64
    %39 = "llvm.mlir.constant"() <{value = 25 : i64}> : () -> i64
    %40 = "llvm.mlir.constant"() <{value = 27 : i64}> : () -> i64
    %41 = "llvm.mlir.constant"() <{value = 28 : i64}> : () -> i64
    %42 = "llvm.mlir.constant"() <{value = 36 : i64}> : () -> i64
    %43 = "llvm.mlir.constant"() <{value = 30 : i64}> : () -> i64
    %44 = "llvm.mlir.constant"() <{value = 44 : i64}> : () -> i64
    %45 = "llvm.load"(%arg1) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %46 = "llvm.getelementptr"(%arg1, %0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %47 = "llvm.load"(%46) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %48 = "llvm.getelementptr"(%arg1, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %49 = "llvm.load"(%48) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %50 = "llvm.getelementptr"(%arg1, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %51 = "llvm.load"(%50) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %52 = "llvm.getelementptr"(%arg1, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %53 = "llvm.load"(%52) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %54 = "llvm.lshr"(%45, %4) : (i64, i64) -> i64
    %55 = "llvm.lshr"(%47, %4) : (i64, i64) -> i64
    %56 = "llvm.lshr"(%49, %4) : (i64, i64) -> i64
    %57 = "llvm.lshr"(%51, %4) : (i64, i64) -> i64
    %58 = "llvm.lshr"(%53, %4) : (i64, i64) -> i64
    %59 = "llvm.and"(%45, %5) : (i64, i64) -> i64
    %60 = "llvm.and"(%47, %5) : (i64, i64) -> i64
    %61 = "llvm.and"(%49, %5) : (i64, i64) -> i64
    %62 = "llvm.and"(%51, %5) : (i64, i64) -> i64
    %63 = "llvm.and"(%53, %5) : (i64, i64) -> i64
    %64 = "llvm.mul"(%58, %6) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %65 = "llvm.add"(%64, %59) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %66 = "llvm.add"(%60, %54) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %67 = "llvm.add"(%61, %55) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %68 = "llvm.add"(%62, %56) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %69 = "llvm.add"(%63, %57) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %70 = "llvm.add"(%65, %6) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %71 = "llvm.lshr"(%70, %4) : (i64, i64) -> i64
    %72 = "llvm.add"(%71, %66) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %73 = "llvm.lshr"(%72, %4) : (i64, i64) -> i64
    %74 = "llvm.add"(%73, %67) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %75 = "llvm.lshr"(%74, %4) : (i64, i64) -> i64
    %76 = "llvm.add"(%75, %68) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %77 = "llvm.lshr"(%76, %4) : (i64, i64) -> i64
    %78 = "llvm.add"(%77, %69) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %79 = "llvm.lshr"(%78, %4) : (i64, i64) -> i64
    %80 = "llvm.mul"(%79, %6) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %81 = "llvm.add"(%80, %65) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %82 = "llvm.lshr"(%81, %4) : (i64, i64) -> i64
    %83 = "llvm.add"(%82, %66) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %84 = "llvm.lshr"(%83, %4) : (i64, i64) -> i64
    %85 = "llvm.add"(%84, %67) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %86 = "llvm.and"(%83, %5) : (i64, i64) -> i64
    %87 = "llvm.lshr"(%85, %4) : (i64, i64) -> i64
    %88 = "llvm.add"(%87, %68) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %89 = "llvm.and"(%85, %5) : (i64, i64) -> i64
    %90 = "llvm.lshr"(%88, %4) : (i64, i64) -> i64
    %91 = "llvm.add"(%90, %69) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %92 = "llvm.and"(%88, %5) : (i64, i64) -> i64
    %93 = "llvm.and"(%91, %5) : (i64, i64) -> i64
    %94 = "llvm.trunc"(%81) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%94, %arg0) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %95 = "llvm.lshr"(%81, %0) : (i64, i64) -> i64
    %96 = "llvm.getelementptr"(%arg0, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %97 = "llvm.trunc"(%95) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%97, %96) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %98 = "llvm.lshr"(%81, %1) : (i64, i64) -> i64
    %99 = "llvm.getelementptr"(%arg0, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %100 = "llvm.trunc"(%98) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%100, %99) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %101 = "llvm.lshr"(%81, %2) : (i64, i64) -> i64
    %102 = "llvm.getelementptr"(%arg0, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %103 = "llvm.trunc"(%101) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%103, %102) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %104 = "llvm.lshr"(%81, %3) : (i64, i64) -> i64
    %105 = "llvm.getelementptr"(%arg0, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %106 = "llvm.trunc"(%104) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%106, %105) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %107 = "llvm.lshr"(%81, %11) : (i64, i64) -> i64
    %108 = "llvm.getelementptr"(%arg0, %12) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %109 = "llvm.trunc"(%107) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%109, %108) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %110 = "llvm.lshr"(%81, %13) : (i64, i64) -> i64
    %111 = "llvm.and"(%110, %14) : (i64, i64) -> i64
    %112 = "llvm.shl"(%86, %9) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %113 = "llvm.or"(%112, %111) <{isDisjoint}> : (i64, i64) -> i64
    %114 = "llvm.getelementptr"(%arg0, %15) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %115 = "llvm.trunc"(%113) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%115, %114) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %116 = "llvm.lshr"(%83, %12) : (i64, i64) -> i64
    %117 = "llvm.getelementptr"(%arg0, %14) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %118 = "llvm.trunc"(%116) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%118, %117) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %119 = "llvm.lshr"(%83, %16) : (i64, i64) -> i64
    %120 = "llvm.getelementptr"(%arg0, %0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %121 = "llvm.trunc"(%119) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%121, %120) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %122 = "llvm.lshr"(%83, %17) : (i64, i64) -> i64
    %123 = "llvm.getelementptr"(%arg0, %18) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %124 = "llvm.trunc"(%122) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%124, %123) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %125 = "llvm.lshr"(%83, %19) : (i64, i64) -> i64
    %126 = "llvm.getelementptr"(%arg0, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %127 = "llvm.trunc"(%125) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%127, %126) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %128 = "llvm.lshr"(%83, %21) : (i64, i64) -> i64
    %129 = "llvm.getelementptr"(%arg0, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %130 = "llvm.trunc"(%128) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%130, %129) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %131 = "llvm.lshr"(%86, %23) : (i64, i64) -> i64
    %132 = "llvm.shl"(%89, %15) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %133 = "llvm.or"(%132, %131) <{isDisjoint}> : (i64, i64) -> i64
    %134 = "llvm.getelementptr"(%arg0, %24) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %135 = "llvm.trunc"(%133) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%135, %134) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %136 = "llvm.lshr"(%85, %8) : (i64, i64) -> i64
    %137 = "llvm.getelementptr"(%arg0, %16) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %138 = "llvm.trunc"(%136) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%138, %137) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %139 = "llvm.lshr"(%85, %20) : (i64, i64) -> i64
    %140 = "llvm.getelementptr"(%arg0, %25) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %141 = "llvm.trunc"(%139) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%141, %140) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %142 = "llvm.lshr"(%85, %26) : (i64, i64) -> i64
    %143 = "llvm.getelementptr"(%arg0, %27) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %144 = "llvm.trunc"(%142) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%144, %143) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %145 = "llvm.lshr"(%85, %28) : (i64, i64) -> i64
    %146 = "llvm.getelementptr"(%arg0, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %147 = "llvm.trunc"(%145) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%147, %146) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %148 = "llvm.lshr"(%85, %29) : (i64, i64) -> i64
    %149 = "llvm.getelementptr"(%arg0, %30) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %150 = "llvm.trunc"(%148) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%150, %149) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %151 = "llvm.lshr"(%85, %31) : (i64, i64) -> i64
    %152 = "llvm.getelementptr"(%arg0, %26) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %153 = "llvm.trunc"(%151) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%153, %152) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %154 = "llvm.lshr"(%89, %32) : (i64, i64) -> i64
    %155 = "llvm.shl"(%92, %7) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %156 = "llvm.or"(%155, %154) <{isDisjoint}> : (i64, i64) -> i64
    %157 = "llvm.getelementptr"(%arg0, %6) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %158 = "llvm.trunc"(%156) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%158, %157) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %159 = "llvm.lshr"(%88, %14) : (i64, i64) -> i64
    %160 = "llvm.getelementptr"(%arg0, %33) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %161 = "llvm.trunc"(%159) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%161, %160) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %162 = "llvm.lshr"(%88, %27) : (i64, i64) -> i64
    %163 = "llvm.getelementptr"(%arg0, %17) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %164 = "llvm.trunc"(%162) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%164, %163) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %165 = "llvm.lshr"(%88, %34) : (i64, i64) -> i64
    %166 = "llvm.getelementptr"(%arg0, %35) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %167 = "llvm.trunc"(%165) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%167, %166) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %168 = "llvm.lshr"(%88, %36) : (i64, i64) -> i64
    %169 = "llvm.getelementptr"(%arg0, %34) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %170 = "llvm.trunc"(%168) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%170, %169) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %171 = "llvm.lshr"(%88, %37) : (i64, i64) -> i64
    %172 = "llvm.getelementptr"(%arg0, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %173 = "llvm.trunc"(%171) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%173, %172) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %174 = "llvm.lshr"(%92, %38) : (i64, i64) -> i64
    %175 = "llvm.shl"(%93, %10) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %176 = "llvm.or"(%175, %174) <{isDisjoint}> : (i64, i64) -> i64
    %177 = "llvm.getelementptr"(%arg0, %39) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %178 = "llvm.trunc"(%176) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%178, %177) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %179 = "llvm.lshr"(%91, %10) : (i64, i64) -> i64
    %180 = "llvm.getelementptr"(%arg0, %28) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %181 = "llvm.trunc"(%179) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%181, %180) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %182 = "llvm.lshr"(%91, %24) : (i64, i64) -> i64
    %183 = "llvm.getelementptr"(%arg0, %40) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %184 = "llvm.trunc"(%182) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%184, %183) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %185 = "llvm.lshr"(%91, %33) : (i64, i64) -> i64
    %186 = "llvm.getelementptr"(%arg0, %41) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %187 = "llvm.trunc"(%185) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%187, %186) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %188 = "llvm.lshr"(%91, %41) : (i64, i64) -> i64
    %189 = "llvm.getelementptr"(%arg0, %19) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %190 = "llvm.trunc"(%188) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%190, %189) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %191 = "llvm.lshr"(%91, %42) : (i64, i64) -> i64
    %192 = "llvm.getelementptr"(%arg0, %43) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %193 = "llvm.trunc"(%191) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%193, %192) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %194 = "llvm.lshr"(%93, %44) : (i64, i64) -> i64
    %195 = "llvm.getelementptr"(%arg0, %36) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %196 = "llvm.trunc"(%194) <{overflowFlags = 3 : i32}> : (i64) -> i8
    "llvm.store"(%196, %195) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

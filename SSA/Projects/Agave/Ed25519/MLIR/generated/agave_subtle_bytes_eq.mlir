"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.noundef}], function_type = !llvm.func<i8 (i8)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], res_attrs = [{llvm.noundef}], sym_name = "_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519", target_cpu = "x86-64", unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
  }) : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<fastcc>, arg_attrs = [{llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], dso_local, function_type = !llvm.func<i8 (ptr, ptr)>, inline_hint, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = read, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], personality = @rust_eh_personality, res_attrs = [{llvm.noundef}], sym_name = "_RNvXs8_Csh8VEmffyqhs_6subtleShNtB5_14ConstantTimeEq5ct_eqCsjK63O35OHGN_14solana_ed25519", target_cpu = "x86-64", unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 1 : i64, will_return}> ({
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %1 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 9 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 10 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 11 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 12 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 13 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = 14 : i64}> : () -> i64
    %15 = "llvm.mlir.constant"() <{value = 15 : i64}> : () -> i64
    %16 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %17 = "llvm.mlir.constant"() <{value = 17 : i64}> : () -> i64
    %18 = "llvm.mlir.constant"() <{value = 18 : i64}> : () -> i64
    %19 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %20 = "llvm.mlir.constant"() <{value = 20 : i64}> : () -> i64
    %21 = "llvm.mlir.constant"() <{value = 21 : i64}> : () -> i64
    %22 = "llvm.mlir.constant"() <{value = 22 : i64}> : () -> i64
    %23 = "llvm.mlir.constant"() <{value = 23 : i64}> : () -> i64
    %24 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> i64
    %25 = "llvm.mlir.constant"() <{value = 25 : i64}> : () -> i64
    %26 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %27 = "llvm.mlir.constant"() <{value = 27 : i64}> : () -> i64
    %28 = "llvm.mlir.constant"() <{value = 28 : i64}> : () -> i64
    %29 = "llvm.mlir.constant"() <{value = 29 : i64}> : () -> i64
    %30 = "llvm.mlir.constant"() <{value = 30 : i64}> : () -> i64
    %31 = "llvm.mlir.constant"() <{value = 31 : i64}> : () -> i64
    %32 = "llvm.load"(%arg0) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %33 = "llvm.load"(%arg1) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %34 = "llvm.icmp"(%32, %33) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %35 = "llvm.zext"(%34) : (i1) -> i8
    %36 = "llvm.call"(%35) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %37 = "llvm.and"(%36, %0) : (i8, i8) -> i8
    %38 = "llvm.getelementptr"(%arg0, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %39 = "llvm.getelementptr"(%arg1, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %40 = "llvm.load"(%38) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %41 = "llvm.load"(%39) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %42 = "llvm.icmp"(%40, %41) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %43 = "llvm.zext"(%42) : (i1) -> i8
    %44 = "llvm.call"(%43) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %45 = "llvm.and"(%44, %37) : (i8, i8) -> i8
    %46 = "llvm.getelementptr"(%arg0, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %47 = "llvm.getelementptr"(%arg1, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %48 = "llvm.load"(%46) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %49 = "llvm.load"(%47) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %50 = "llvm.icmp"(%48, %49) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %51 = "llvm.zext"(%50) : (i1) -> i8
    %52 = "llvm.call"(%51) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %53 = "llvm.and"(%52, %45) : (i8, i8) -> i8
    %54 = "llvm.getelementptr"(%arg0, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %55 = "llvm.getelementptr"(%arg1, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %56 = "llvm.load"(%54) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %57 = "llvm.load"(%55) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %58 = "llvm.icmp"(%56, %57) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %59 = "llvm.zext"(%58) : (i1) -> i8
    %60 = "llvm.call"(%59) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %61 = "llvm.and"(%60, %53) : (i8, i8) -> i8
    %62 = "llvm.getelementptr"(%arg0, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %63 = "llvm.getelementptr"(%arg1, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %64 = "llvm.load"(%62) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %65 = "llvm.load"(%63) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %66 = "llvm.icmp"(%64, %65) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %67 = "llvm.zext"(%66) : (i1) -> i8
    %68 = "llvm.call"(%67) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %69 = "llvm.and"(%68, %61) : (i8, i8) -> i8
    %70 = "llvm.getelementptr"(%arg0, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %71 = "llvm.getelementptr"(%arg1, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %72 = "llvm.load"(%70) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %73 = "llvm.load"(%71) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %74 = "llvm.icmp"(%72, %73) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %75 = "llvm.zext"(%74) : (i1) -> i8
    %76 = "llvm.call"(%75) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %77 = "llvm.and"(%76, %69) : (i8, i8) -> i8
    %78 = "llvm.getelementptr"(%arg0, %6) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %79 = "llvm.getelementptr"(%arg1, %6) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %80 = "llvm.load"(%78) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %81 = "llvm.load"(%79) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %82 = "llvm.icmp"(%80, %81) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %83 = "llvm.zext"(%82) : (i1) -> i8
    %84 = "llvm.call"(%83) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %85 = "llvm.and"(%84, %77) : (i8, i8) -> i8
    %86 = "llvm.getelementptr"(%arg0, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %87 = "llvm.getelementptr"(%arg1, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %88 = "llvm.load"(%86) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %89 = "llvm.load"(%87) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %90 = "llvm.icmp"(%88, %89) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %91 = "llvm.zext"(%90) : (i1) -> i8
    %92 = "llvm.call"(%91) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %93 = "llvm.and"(%92, %85) : (i8, i8) -> i8
    %94 = "llvm.getelementptr"(%arg0, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %95 = "llvm.getelementptr"(%arg1, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %96 = "llvm.load"(%94) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %97 = "llvm.load"(%95) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %98 = "llvm.icmp"(%96, %97) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %99 = "llvm.zext"(%98) : (i1) -> i8
    %100 = "llvm.call"(%99) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %101 = "llvm.and"(%100, %93) : (i8, i8) -> i8
    %102 = "llvm.getelementptr"(%arg0, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %103 = "llvm.getelementptr"(%arg1, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %104 = "llvm.load"(%102) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %105 = "llvm.load"(%103) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %106 = "llvm.icmp"(%104, %105) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %107 = "llvm.zext"(%106) : (i1) -> i8
    %108 = "llvm.call"(%107) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %109 = "llvm.and"(%108, %101) : (i8, i8) -> i8
    %110 = "llvm.getelementptr"(%arg0, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %111 = "llvm.getelementptr"(%arg1, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %112 = "llvm.load"(%110) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %113 = "llvm.load"(%111) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %114 = "llvm.icmp"(%112, %113) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %115 = "llvm.zext"(%114) : (i1) -> i8
    %116 = "llvm.call"(%115) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %117 = "llvm.and"(%116, %109) : (i8, i8) -> i8
    %118 = "llvm.getelementptr"(%arg0, %11) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %119 = "llvm.getelementptr"(%arg1, %11) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %120 = "llvm.load"(%118) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %121 = "llvm.load"(%119) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %122 = "llvm.icmp"(%120, %121) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %123 = "llvm.zext"(%122) : (i1) -> i8
    %124 = "llvm.call"(%123) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %125 = "llvm.and"(%124, %117) : (i8, i8) -> i8
    %126 = "llvm.getelementptr"(%arg0, %12) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %127 = "llvm.getelementptr"(%arg1, %12) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %128 = "llvm.load"(%126) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %129 = "llvm.load"(%127) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %130 = "llvm.icmp"(%128, %129) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %131 = "llvm.zext"(%130) : (i1) -> i8
    %132 = "llvm.call"(%131) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %133 = "llvm.and"(%132, %125) : (i8, i8) -> i8
    %134 = "llvm.getelementptr"(%arg0, %13) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %135 = "llvm.getelementptr"(%arg1, %13) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %136 = "llvm.load"(%134) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %137 = "llvm.load"(%135) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %138 = "llvm.icmp"(%136, %137) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %139 = "llvm.zext"(%138) : (i1) -> i8
    %140 = "llvm.call"(%139) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %141 = "llvm.and"(%140, %133) : (i8, i8) -> i8
    %142 = "llvm.getelementptr"(%arg0, %14) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %143 = "llvm.getelementptr"(%arg1, %14) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %144 = "llvm.load"(%142) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %145 = "llvm.load"(%143) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %146 = "llvm.icmp"(%144, %145) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %147 = "llvm.zext"(%146) : (i1) -> i8
    %148 = "llvm.call"(%147) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %149 = "llvm.and"(%148, %141) : (i8, i8) -> i8
    %150 = "llvm.getelementptr"(%arg0, %15) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %151 = "llvm.getelementptr"(%arg1, %15) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %152 = "llvm.load"(%150) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %153 = "llvm.load"(%151) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %154 = "llvm.icmp"(%152, %153) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %155 = "llvm.zext"(%154) : (i1) -> i8
    %156 = "llvm.call"(%155) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %157 = "llvm.and"(%156, %149) : (i8, i8) -> i8
    %158 = "llvm.getelementptr"(%arg0, %16) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %159 = "llvm.getelementptr"(%arg1, %16) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %160 = "llvm.load"(%158) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %161 = "llvm.load"(%159) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %162 = "llvm.icmp"(%160, %161) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %163 = "llvm.zext"(%162) : (i1) -> i8
    %164 = "llvm.call"(%163) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %165 = "llvm.and"(%164, %157) : (i8, i8) -> i8
    %166 = "llvm.getelementptr"(%arg0, %17) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %167 = "llvm.getelementptr"(%arg1, %17) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %168 = "llvm.load"(%166) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %169 = "llvm.load"(%167) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %170 = "llvm.icmp"(%168, %169) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %171 = "llvm.zext"(%170) : (i1) -> i8
    %172 = "llvm.call"(%171) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %173 = "llvm.and"(%172, %165) : (i8, i8) -> i8
    %174 = "llvm.getelementptr"(%arg0, %18) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %175 = "llvm.getelementptr"(%arg1, %18) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %176 = "llvm.load"(%174) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %177 = "llvm.load"(%175) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %178 = "llvm.icmp"(%176, %177) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %179 = "llvm.zext"(%178) : (i1) -> i8
    %180 = "llvm.call"(%179) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %181 = "llvm.and"(%180, %173) : (i8, i8) -> i8
    %182 = "llvm.getelementptr"(%arg0, %19) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %183 = "llvm.getelementptr"(%arg1, %19) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %184 = "llvm.load"(%182) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %185 = "llvm.load"(%183) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %186 = "llvm.icmp"(%184, %185) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %187 = "llvm.zext"(%186) : (i1) -> i8
    %188 = "llvm.call"(%187) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %189 = "llvm.and"(%188, %181) : (i8, i8) -> i8
    %190 = "llvm.getelementptr"(%arg0, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %191 = "llvm.getelementptr"(%arg1, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %192 = "llvm.load"(%190) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %193 = "llvm.load"(%191) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %194 = "llvm.icmp"(%192, %193) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %195 = "llvm.zext"(%194) : (i1) -> i8
    %196 = "llvm.call"(%195) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %197 = "llvm.and"(%196, %189) : (i8, i8) -> i8
    %198 = "llvm.getelementptr"(%arg0, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %199 = "llvm.getelementptr"(%arg1, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %200 = "llvm.load"(%198) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %201 = "llvm.load"(%199) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %202 = "llvm.icmp"(%200, %201) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %203 = "llvm.zext"(%202) : (i1) -> i8
    %204 = "llvm.call"(%203) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %205 = "llvm.and"(%204, %197) : (i8, i8) -> i8
    %206 = "llvm.getelementptr"(%arg0, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %207 = "llvm.getelementptr"(%arg1, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %208 = "llvm.load"(%206) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %209 = "llvm.load"(%207) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %210 = "llvm.icmp"(%208, %209) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %211 = "llvm.zext"(%210) : (i1) -> i8
    %212 = "llvm.call"(%211) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %213 = "llvm.and"(%212, %205) : (i8, i8) -> i8
    %214 = "llvm.getelementptr"(%arg0, %23) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %215 = "llvm.getelementptr"(%arg1, %23) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %216 = "llvm.load"(%214) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %217 = "llvm.load"(%215) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %218 = "llvm.icmp"(%216, %217) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %219 = "llvm.zext"(%218) : (i1) -> i8
    %220 = "llvm.call"(%219) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %221 = "llvm.and"(%220, %213) : (i8, i8) -> i8
    %222 = "llvm.getelementptr"(%arg0, %24) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %223 = "llvm.getelementptr"(%arg1, %24) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %224 = "llvm.load"(%222) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %225 = "llvm.load"(%223) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %226 = "llvm.icmp"(%224, %225) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %227 = "llvm.zext"(%226) : (i1) -> i8
    %228 = "llvm.call"(%227) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %229 = "llvm.and"(%228, %221) : (i8, i8) -> i8
    %230 = "llvm.getelementptr"(%arg0, %25) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %231 = "llvm.getelementptr"(%arg1, %25) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %232 = "llvm.load"(%230) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %233 = "llvm.load"(%231) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %234 = "llvm.icmp"(%232, %233) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %235 = "llvm.zext"(%234) : (i1) -> i8
    %236 = "llvm.call"(%235) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %237 = "llvm.and"(%236, %229) : (i8, i8) -> i8
    %238 = "llvm.getelementptr"(%arg0, %26) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %239 = "llvm.getelementptr"(%arg1, %26) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %240 = "llvm.load"(%238) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %241 = "llvm.load"(%239) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %242 = "llvm.icmp"(%240, %241) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %243 = "llvm.zext"(%242) : (i1) -> i8
    %244 = "llvm.call"(%243) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %245 = "llvm.and"(%244, %237) : (i8, i8) -> i8
    %246 = "llvm.getelementptr"(%arg0, %27) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %247 = "llvm.getelementptr"(%arg1, %27) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %248 = "llvm.load"(%246) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %249 = "llvm.load"(%247) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %250 = "llvm.icmp"(%248, %249) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %251 = "llvm.zext"(%250) : (i1) -> i8
    %252 = "llvm.call"(%251) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %253 = "llvm.and"(%252, %245) : (i8, i8) -> i8
    %254 = "llvm.getelementptr"(%arg0, %28) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %255 = "llvm.getelementptr"(%arg1, %28) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %256 = "llvm.load"(%254) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %257 = "llvm.load"(%255) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %258 = "llvm.icmp"(%256, %257) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %259 = "llvm.zext"(%258) : (i1) -> i8
    %260 = "llvm.call"(%259) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %261 = "llvm.and"(%260, %253) : (i8, i8) -> i8
    %262 = "llvm.getelementptr"(%arg0, %29) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %263 = "llvm.getelementptr"(%arg1, %29) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %264 = "llvm.load"(%262) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %265 = "llvm.load"(%263) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %266 = "llvm.icmp"(%264, %265) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %267 = "llvm.zext"(%266) : (i1) -> i8
    %268 = "llvm.call"(%267) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %269 = "llvm.and"(%268, %261) : (i8, i8) -> i8
    %270 = "llvm.getelementptr"(%arg0, %30) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %271 = "llvm.getelementptr"(%arg1, %30) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %272 = "llvm.load"(%270) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %273 = "llvm.load"(%271) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %274 = "llvm.icmp"(%272, %273) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %275 = "llvm.zext"(%274) : (i1) -> i8
    %276 = "llvm.call"(%275) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %277 = "llvm.and"(%276, %269) : (i8, i8) -> i8
    %278 = "llvm.getelementptr"(%arg0, %31) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %279 = "llvm.getelementptr"(%arg1, %31) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %280 = "llvm.load"(%278) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %281 = "llvm.load"(%279) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %282 = "llvm.icmp"(%280, %281) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %283 = "llvm.zext"(%282) : (i1) -> i8
    %284 = "llvm.call"(%283) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %285 = "llvm.and"(%284, %277) : (i8, i8) -> i8
    %286 = "llvm.call"(%285) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    "llvm.return"(%286) : (i8) -> ()
  }) : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<i32 (...)>, linkage = #llvm.linkage<external>, passthrough = ["nonlazybind", ["target-cpu", "x86-64"]], sym_name = "rust_eh_personality", target_cpu = "x86-64", unnamed_addr = 2 : i64, visibility_ = 0 : i64}> ({
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

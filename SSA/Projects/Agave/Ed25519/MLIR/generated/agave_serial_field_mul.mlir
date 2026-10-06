"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.noundef, llvm.sret = !llvm.array<40 x i8>, llvm.writeonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.noundef, llvm.readonly}], function_type = !llvm.func<void (ptr, ptr, ptr)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], sym_name = "_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul", target_cpu = "x86-64", unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 51 : i128}> : () -> i128
    %6 = "llvm.mlir.constant"() <{value = 18446744073709551615 : i128}> : () -> i128
    %7 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %9 = "llvm.getelementptr"(%arg2, %0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %10 = "llvm.load"(%9) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %11 = "llvm.mul"(%10, %1) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %12 = "llvm.getelementptr"(%arg2, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %13 = "llvm.load"(%12) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %14 = "llvm.mul"(%13, %1) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %15 = "llvm.getelementptr"(%arg2, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %16 = "llvm.load"(%15) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %17 = "llvm.mul"(%16, %1) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %18 = "llvm.getelementptr"(%arg2, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %19 = "llvm.load"(%18) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %20 = "llvm.mul"(%19, %1) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %21 = "llvm.load"(%arg1) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %22 = "llvm.load"(%arg2) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %23 = "llvm.zext"(%21) : (i64) -> i128
    %24 = "llvm.zext"(%22) : (i64) -> i128
    %25 = "llvm.mul"(%24, %23) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %26 = "llvm.getelementptr"(%arg1, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %27 = "llvm.load"(%26) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %28 = "llvm.zext"(%27) : (i64) -> i128
    %29 = "llvm.zext"(%11) : (i64) -> i128
    %30 = "llvm.mul"(%28, %29) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %31 = "llvm.add"(%30, %25) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %32 = "llvm.getelementptr"(%arg1, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %33 = "llvm.load"(%32) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %34 = "llvm.zext"(%33) : (i64) -> i128
    %35 = "llvm.zext"(%14) : (i64) -> i128
    %36 = "llvm.mul"(%34, %35) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %37 = "llvm.add"(%31, %36) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %38 = "llvm.getelementptr"(%arg1, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %39 = "llvm.load"(%38) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %40 = "llvm.zext"(%39) : (i64) -> i128
    %41 = "llvm.zext"(%17) : (i64) -> i128
    %42 = "llvm.mul"(%40, %41) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %43 = "llvm.add"(%37, %42) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %44 = "llvm.getelementptr"(%arg1, %0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %45 = "llvm.load"(%44) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %46 = "llvm.zext"(%45) : (i64) -> i128
    %47 = "llvm.zext"(%20) : (i64) -> i128
    %48 = "llvm.mul"(%46, %47) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %49 = "llvm.add"(%43, %48) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %50 = "llvm.mul"(%46, %24) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %51 = "llvm.zext"(%10) : (i64) -> i128
    %52 = "llvm.mul"(%23, %51) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %53 = "llvm.mul"(%28, %35) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %54 = "llvm.mul"(%34, %41) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %55 = "llvm.mul"(%40, %47) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %56 = "llvm.mul"(%40, %24) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %57 = "llvm.mul"(%46, %51) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %58 = "llvm.zext"(%13) : (i64) -> i128
    %59 = "llvm.mul"(%23, %58) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %60 = "llvm.mul"(%28, %41) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %61 = "llvm.mul"(%34, %47) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %62 = "llvm.mul"(%34, %24) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %63 = "llvm.mul"(%40, %51) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %64 = "llvm.mul"(%46, %58) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %65 = "llvm.zext"(%16) : (i64) -> i128
    %66 = "llvm.mul"(%23, %65) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %67 = "llvm.mul"(%28, %47) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %68 = "llvm.mul"(%28, %24) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %69 = "llvm.mul"(%34, %51) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %70 = "llvm.mul"(%40, %58) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %71 = "llvm.mul"(%46, %65) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %72 = "llvm.zext"(%19) : (i64) -> i128
    %73 = "llvm.mul"(%23, %72) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %74 = "llvm.lshr"(%49, %5) : (i128, i128) -> i128
    %75 = "llvm.and"(%74, %6) : (i128, i128) -> i128
    %76 = "llvm.add"(%53, %52) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %77 = "llvm.add"(%76, %54) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %78 = "llvm.add"(%77, %55) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %79 = "llvm.add"(%78, %50) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %80 = "llvm.add"(%79, %75) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %81 = "llvm.trunc"(%49) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %82 = "llvm.and"(%81, %7) : (i64, i64) -> i64
    %83 = "llvm.lshr"(%80, %5) : (i128, i128) -> i128
    %84 = "llvm.and"(%83, %6) : (i128, i128) -> i128
    %85 = "llvm.add"(%60, %59) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %86 = "llvm.add"(%85, %61) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %87 = "llvm.add"(%86, %56) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %88 = "llvm.add"(%87, %57) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %89 = "llvm.add"(%88, %84) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %90 = "llvm.trunc"(%80) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %91 = "llvm.and"(%90, %7) : (i64, i64) -> i64
    %92 = "llvm.lshr"(%89, %5) : (i128, i128) -> i128
    %93 = "llvm.and"(%92, %6) : (i128, i128) -> i128
    %94 = "llvm.add"(%67, %66) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %95 = "llvm.add"(%94, %62) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %96 = "llvm.add"(%95, %63) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %97 = "llvm.add"(%96, %64) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %98 = "llvm.add"(%97, %93) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %99 = "llvm.trunc"(%89) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %100 = "llvm.and"(%99, %7) : (i64, i64) -> i64
    %101 = "llvm.lshr"(%98, %5) : (i128, i128) -> i128
    %102 = "llvm.and"(%101, %6) : (i128, i128) -> i128
    %103 = "llvm.add"(%68, %73) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %104 = "llvm.add"(%103, %69) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %105 = "llvm.add"(%104, %70) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %106 = "llvm.add"(%105, %71) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %107 = "llvm.add"(%106, %102) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %108 = "llvm.trunc"(%98) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %109 = "llvm.and"(%108, %7) : (i64, i64) -> i64
    %110 = "llvm.lshr"(%107, %5) : (i128, i128) -> i128
    %111 = "llvm.trunc"(%110) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %112 = "llvm.trunc"(%107) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %113 = "llvm.and"(%112, %7) : (i64, i64) -> i64
    %114 = "llvm.mul"(%111, %1) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %115 = "llvm.add"(%114, %82) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %116 = "llvm.lshr"(%115, %8) : (i64, i64) -> i64
    %117 = "llvm.add"(%116, %91) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %118 = "llvm.and"(%115, %7) : (i64, i64) -> i64
    "llvm.store"(%118, %arg0) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %119 = "llvm.getelementptr"(%arg0, %0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%117, %119) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %120 = "llvm.getelementptr"(%arg0, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%100, %120) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %121 = "llvm.getelementptr"(%arg0, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%109, %121) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %122 = "llvm.getelementptr"(%arg0, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%113, %122) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

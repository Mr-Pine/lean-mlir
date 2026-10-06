#alias_scope_domain = #llvm.alias_scope_domain<id = distinct[0]<>, description = "_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x46reduceB1a_NtB2_15___Impl_reduce__12__impl_reduce">
#alias_scope = #llvm.alias_scope<id = distinct[1]<>, domain = #alias_scope_domain, description = "_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x46reduceB1a_NtB2_15___Impl_reduce__12__impl_reduce: %_0">
#alias_scope1 = #llvm.alias_scope<id = distinct[2]<>, domain = #alias_scope_domain, description = "_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x46reduceB1a_NtB2_15___Impl_reduce__12__impl_reduce: %self">
"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.noundef, llvm.sret = !llvm.array<160 x i8>, llvm.writeonly}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.noundef, llvm.readonly}], function_type = !llvm.func<void (ptr, ptr)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], sym_name = "agave_avx2_field_reduce", target_cpu = "x86-64", target_features = #llvm.target_features<["+avx", "+avx2", "+sse", "+sse2", "+sse3", "+sse4.1", "+sse4.2", "+crc32", "+ssse3"]>, unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 64 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 96 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 128 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = dense<[26, 26, 25, 25, 26, 26, 25, 25]> : vector<8xi32>}> : () -> vector<8xi32>
    %5 = "llvm.mlir.poison"() : () -> i32
    %6 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %7 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %8 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %9 = "llvm.insertelement"(%7, %6, %8) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %10 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %11 = "llvm.insertelement"(%9, %6, %10) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %12 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %13 = "llvm.insertelement"(%11, %5, %12) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %14 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %15 = "llvm.insertelement"(%13, %5, %14) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %16 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %17 = "llvm.insertelement"(%15, %6, %16) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %18 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %19 = "llvm.insertelement"(%17, %6, %18) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %20 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %21 = "llvm.insertelement"(%19, %5, %20) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %22 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %23 = "llvm.insertelement"(%21, %5, %22) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %24 = "llvm.mlir.constant"() <{value = dense<[67108863, 67108863, 33554431, 33554431, 67108863, 67108863, 33554431, 33554431]> : vector<8xi32>}> : () -> vector<8xi32>
    %25 = "llvm.mlir.constant"() <{value = dense<[0, 0, 127, 127, 0, 0, 127, 127]> : vector<8xi32>}> : () -> vector<8xi32>
    %26 = "llvm.mlir.poison"() : () -> vector<8xi32>
    %27 = "llvm.mlir.constant"() <{value = dense<19> : vector<4xi64>}> : () -> vector<4xi64>
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope1}> : () -> ()
    %28 = "llvm.load"(%arg1) <{alias_scopes = [#alias_scope1], alignment = 32 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %29 = "llvm.getelementptr"(%arg1, %0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %30 = "llvm.load"(%29) <{alias_scopes = [#alias_scope1], alignment = 32 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %31 = "llvm.getelementptr"(%arg1, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %32 = "llvm.load"(%31) <{alias_scopes = [#alias_scope1], alignment = 32 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %33 = "llvm.getelementptr"(%arg1, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %34 = "llvm.load"(%33) <{alias_scopes = [#alias_scope1], alignment = 32 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %35 = "llvm.getelementptr"(%arg1, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %36 = "llvm.load"(%35) <{alias_scopes = [#alias_scope1], alignment = 32 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %37 = "llvm.lshr"(%28, %4) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %38 = "llvm.shufflevector"(%23, %37) <{mask = array<i32: 0, 1, 8, 9, 4, 5, 12, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %39 = "llvm.and"(%28, %24) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %40 = "llvm.add"(%38, %39) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %41 = "llvm.lshr"(%30, %4) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %42 = "llvm.shufflevector"(%37, %41) <{mask = array<i32: 2, 3, 8, 9, 6, 7, 12, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %43 = "llvm.and"(%30, %24) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %44 = "llvm.add"(%42, %43) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %45 = "llvm.lshr"(%32, %4) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %46 = "llvm.shufflevector"(%41, %45) <{mask = array<i32: 2, 3, 8, 9, 6, 7, 12, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %47 = "llvm.and"(%32, %24) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %48 = "llvm.add"(%46, %47) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %49 = "llvm.lshr"(%34, %4) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %50 = "llvm.shufflevector"(%45, %49) <{mask = array<i32: 2, 3, 8, 9, 6, 7, 12, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %51 = "llvm.and"(%34, %24) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %52 = "llvm.add"(%50, %51) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %53 = "llvm.lshr"(%36, %4) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %54 = "llvm.shufflevector"(%49, %53) <{mask = array<i32: 2, 3, 8, 9, 6, 7, 12, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %55 = "llvm.and"(%36, %24) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %56 = "llvm.add"(%54, %55) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %57 = "llvm.and"(%53, %25) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %58 = "llvm.shufflevector"(%57, %26) <{mask = array<i32: 2, 0, 3, 1, 6, 4, 7, 5>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %59 = "llvm.bitcast"(%58) : (vector<8xi32>) -> vector<4xi64>
    %60 = "llvm.mul"(%59, %27) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %61 = "llvm.bitcast"(%60) : (vector<4xi64>) -> vector<8xi32>
    %62 = "llvm.shufflevector"(%61, %26) <{mask = array<i32: 0, 2, 1, 3, 4, 6, 5, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %63 = "llvm.add"(%40, %62) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%63, %arg0) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %64 = "llvm.getelementptr"(%arg0, %0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%44, %64) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %65 = "llvm.getelementptr"(%arg0, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%48, %65) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %66 = "llvm.getelementptr"(%arg0, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%52, %66) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %67 = "llvm.getelementptr"(%arg0, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%56, %67) <{alias_scopes = [#alias_scope], alignment = 32 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

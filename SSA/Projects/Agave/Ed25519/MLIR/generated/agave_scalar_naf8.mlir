#alias_scope_domain = #llvm.alias_scope_domain<id = distinct[0]<>, description = "_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form">
#alias_scope_domain1 = #llvm.alias_scope_domain<id = distinct[1]<>, description = "_RNvNtCsjK63O35OHGN_14solana_ed255196scalar16read_le_u64_into">
#alias_scope = #llvm.alias_scope<id = distinct[2]<>, domain = #alias_scope_domain, description = "_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form: %naf">
#alias_scope1 = #llvm.alias_scope<id = distinct[3]<>, domain = #alias_scope_domain, description = "_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form: %self">
#alias_scope2 = #llvm.alias_scope<id = distinct[4]<>, domain = #alias_scope_domain1, description = "_RNvNtCsjK63O35OHGN_14solana_ed255196scalar16read_le_u64_into: %dst.0">
#alias_scope3 = #llvm.alias_scope<id = distinct[5]<>, domain = #alias_scope_domain1, description = "_RNvNtCsjK63O35OHGN_14solana_ed255196scalar16read_le_u64_into: %src.0">
"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.align = 1 : i64, llvm.dereferenceable = 256 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.noundef, llvm.sret = !llvm.array<256 x i8>, llvm.writeonly}, {llvm.dereferenceable = 32 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.noundef, llvm.readonly}], function_type = !llvm.func<void (ptr, ptr)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["nofree", "norecurse", "nosync", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], personality = @rust_eh_personality, sym_name = "agave_scalar_naf8", target_cpu = "x86-64", unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64}> ({
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %2 = "llvm.mlir.constant"() <{value = 256 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 63 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 56 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 255 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 127 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 248 : i64}> : () -> i64
    %13 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope}> : () -> ()
    "llvm.intr.memset"(%arg0, %1, %2) <{alias_scopes = [#alias_scope], arg_attrs = [{llvm.align = 1 : i64, llvm.dereferenceable = 256 : i64, llvm.nonnull, llvm.noundef}, {}, {}], isVolatile = false, noalias_scopes = [#alias_scope1]}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.intr.lifetime.start"(%13) : (!llvm.ptr) -> ()
    %14 = "llvm.getelementptr"(%13, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%4, %14) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.intr.memcpy"(%13, %arg1, %3) <{alias_scopes = [#alias_scope2, #alias_scope3], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 1 : i64, llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef, llvm.readonly}, {}], isVolatile = false, noalias_scopes = [#alias_scope]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.br"(%4, %4)[^bb1] : (i64, i64) -> ()
  ^bb1(%15: i64, %16: i64):  // 2 preds: ^bb0, ^bb6
    "llvm.br"(%15)[^bb2] : (i64) -> ()
  ^bb2(%17: i64):  // 2 preds: ^bb1, ^bb5
    %18 = "llvm.lshr"(%17, %5) : (i64, i64) -> i64
    %19 = "llvm.and"(%17, %6) : (i64, i64) -> i64
    %20 = "llvm.icmp"(%19, %7) <{predicate = 6 : i64}> : (i64, i64) -> i1
    %21 = "llvm.getelementptr"(%13, %18) <{elem_type = i64, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %22 = "llvm.load"(%21) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %23 = "llvm.lshr"(%22, %19) : (i64, i64) -> i64
    "llvm.cond_br"(%20, %23)[^bb4, ^bb3] <{operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, i64) -> ()
  ^bb3:  // pred: ^bb2
    %24 = "llvm.getelementptr"(%21, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %25 = "llvm.load"(%24) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %26 = "llvm.sub"(%4, %17) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %27 = "llvm.and"(%26, %6) : (i64, i64) -> i64
    %28 = "llvm.shl"(%25, %27) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %29 = "llvm.or"(%28, %23) : (i64, i64) -> i64
    "llvm.br"(%29)[^bb4] : (i64) -> ()
  ^bb4(%30: i64):  // 2 preds: ^bb2, ^bb3
    %31 = "llvm.and"(%30, %9) : (i64, i64) -> i64
    %32 = "llvm.add"(%31, %16) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %33 = "llvm.and"(%32, %10) : (i64, i64) -> i64
    %34 = "llvm.icmp"(%33, %4) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%34)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb5:  // pred: ^bb4
    %35 = "llvm.add"(%17, %10) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %36 = "llvm.icmp"(%35, %2) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%36, %35)[^bb7, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i64) -> ()
  ^bb6:  // pred: ^bb4
    %37 = "llvm.icmp"(%32, %11) <{predicate = 8 : i64}> : (i64, i64) -> i1
    %38 = "llvm.trunc"(%32) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %39 = "llvm.zext"(%37) : (i1) -> i64
    %40 = "llvm.getelementptr"(%arg0, %17) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%38, %40) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %41 = "llvm.add"(%17, %8) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %42 = "llvm.icmp"(%17, %12) <{predicate = 6 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%42, %41, %39)[^bb1, ^bb7] <{operandSegmentSizes = array<i32: 1, 2, 0>}> : (i1, i64, i64) -> ()
  ^bb7:  // 2 preds: ^bb5, ^bb6
    "llvm.intr.lifetime.end"(%13) : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<i32 (...)>, linkage = #llvm.linkage<external>, passthrough = ["nonlazybind", ["target-cpu", "x86-64"]], sym_name = "rust_eh_personality", target_cpu = "x86-64", unnamed_addr = 2 : i64, visibility_ = 0 : i64}> ({
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

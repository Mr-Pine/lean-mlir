#alias_scope_domain = #llvm.alias_scope_domain<id = distinct[0]<>, description = "fd_memcpy">
#alias_scope_domain1 = #llvm.alias_scope_domain<id = distinct[1]<>, description = "fd_memcpy">
#alias_scope_domain2 = #llvm.alias_scope_domain<id = distinct[2]<>, description = "fd_memcpy">
#tbaa_root = #llvm.tbaa_root<id = "Simple C/C++ TBAA">
#alias_scope = #llvm.alias_scope<id = distinct[3]<>, domain = #alias_scope_domain, description = "fd_memcpy: argument 0">
#alias_scope1 = #llvm.alias_scope<id = distinct[4]<>, domain = #alias_scope_domain, description = "fd_memcpy: argument 1">
#alias_scope2 = #llvm.alias_scope<id = distinct[5]<>, domain = #alias_scope_domain1, description = "fd_memcpy: argument 0">
#alias_scope3 = #llvm.alias_scope<id = distinct[6]<>, domain = #alias_scope_domain1, description = "fd_memcpy: argument 1">
#alias_scope4 = #llvm.alias_scope<id = distinct[7]<>, domain = #alias_scope_domain2, description = "fd_memcpy: argument 0">
#alias_scope5 = #llvm.alias_scope<id = distinct[8]<>, domain = #alias_scope_domain2, description = "fd_memcpy: argument 1">
#tbaa_type_desc = #llvm.tbaa_type_desc<id = "omnipotent char", members = {<#tbaa_root, 0>}>
#tbaa_type_desc1 = #llvm.tbaa_type_desc<id = "long", members = {<#tbaa_type_desc, 0>}>
#tbaa_type_desc2 = #llvm.tbaa_type_desc<id = "fd_sha512_private", members = {<#tbaa_type_desc, 0>, <#tbaa_type_desc, 128>, <#tbaa_type_desc1, 192>, <#tbaa_type_desc1, 200>, <#tbaa_type_desc1, 208>, <#tbaa_type_desc1, 216>}>
#tbaa_tag = #llvm.tbaa_tag<base_type = #tbaa_type_desc2, access_type = #tbaa_type_desc1, offset = 200>
#tbaa_tag1 = #llvm.tbaa_tag<base_type = #tbaa_type_desc2, access_type = #tbaa_type_desc1, offset = 208>
#tbaa_tag2 = #llvm.tbaa_tag<base_type = #tbaa_type_desc2, access_type = #tbaa_type_desc1, offset = 216>
"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<error, "wchar_size", 4 : i32>, #llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<max, "PIE Level", 2 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.noundef, llvm.returned}, {llvm.nocapture, llvm.noundef, llvm.readonly}, {llvm.noundef}], dso_local, function_type = !llvm.func<ptr (ptr, ptr, i64)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["nofree", "norecurse", "nosync", ["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], res_attrs = [{llvm.noundef}], sym_name = "fd_sha512_append", target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", unnamed_addr = 1 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64}> ({
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: i64):
    %0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 128 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 200 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 208 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 216 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 61 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 127 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = -128 : i64}> : () -> i64
    %11 = "llvm.icmp"(%arg2, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%11)[^bb10, ^bb1] <{branch_weights = array<i32: 1, 2000>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:  // pred: ^bb0
    %12 = "llvm.getelementptr"(%arg0, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %13 = "llvm.getelementptr"(%arg0, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %14 = "llvm.load"(%13) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> i64
    %15 = "llvm.getelementptr"(%arg0, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %16 = "llvm.load"(%15) <{alignment = 16 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %17 = "llvm.getelementptr"(%arg0, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %18 = "llvm.load"(%17) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (!llvm.ptr) -> i64
    %19 = "llvm.shl"(%arg2, %5) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %20 = "llvm.add"(%16, %19) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %21 = "llvm.lshr"(%arg2, %6) : (i64, i64) -> i64
    %22 = "llvm.add"(%18, %21) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %23 = "llvm.icmp"(%20, %16) <{predicate = 6 : i64}> : (i64, i64) -> i1
    %24 = "llvm.zext"(%23) : (i1) -> i64
    %25 = "llvm.add"(%22, %24) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    "llvm.store"(%20, %15) <{alignment = 16 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%25, %17) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag2]}> : (i64, !llvm.ptr) -> ()
    %26 = "llvm.icmp"(%14, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%26, %arg1, %arg2)[^bb6, ^bb2] <{branch_weights = array<i32: 2000, 1>, operandSegmentSizes = array<i32: 1, 2, 0>}> : (i1, !llvm.ptr, i64) -> ()
  ^bb2:  // pred: ^bb1
    %27 = "llvm.sub"(%1, %14) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %28 = "llvm.icmp"(%arg2, %27) <{predicate = 6 : i64}> : (i64, i64) -> i1
    %29 = "llvm.getelementptr"(%arg0, %14) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.cond_br"(%28)[^bb3, ^bb4] <{branch_weights = array<i32: 1, 2000>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb3:  // pred: ^bb2
    "llvm.intr.memcpy"(%29, %arg1, %arg2) <{alias_scopes = [#alias_scope, #alias_scope1], arg_attrs = [{llvm.align = 1 : i64, llvm.nonnull}, {llvm.align = 1 : i64, llvm.readonly}, {}], isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %30 = "llvm.add"(%14, %arg2) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    "llvm.br"(%30, %arg1, %arg2)[^bb5] : (i64, !llvm.ptr, i64) -> ()
  ^bb4:  // pred: ^bb2
    "llvm.intr.memcpy"(%29, %arg1, %27) <{alias_scopes = [#alias_scope2, #alias_scope3], arg_attrs = [{llvm.align = 1 : i64, llvm.nonnull}, {llvm.align = 1 : i64, llvm.readonly}, {}], isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %31 = "llvm.getelementptr"(%arg1, %27) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %32 = "llvm.sub"(%arg2, %27) <{overflowFlags = 2 : i32}> : (i64, i64) -> i64
    "llvm.call"(%12, %arg0, %7) <{CConv = #llvm.cconv<fastcc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.nonnull, llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @fd_sha512_core_ref, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.br"(%0, %31, %32)[^bb5] : (i64, !llvm.ptr, i64) -> ()
  ^bb5(%33: i64, %34: !llvm.ptr, %35: i64):  // 2 preds: ^bb3, ^bb4
    "llvm.store"(%33, %13) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    "llvm.cond_br"(%28, %34, %35)[^bb10, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 2>}> : (i1, !llvm.ptr, i64) -> ()
  ^bb6(%36: !llvm.ptr, %37: i64):  // 2 preds: ^bb1, ^bb5
    %38 = "llvm.icmp"(%37, %1) <{predicate = 6 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%38)[^bb8, ^bb7] <{branch_weights = array<i32: 1, 2000>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb7:  // pred: ^bb6
    %39 = "llvm.lshr"(%37, %8) : (i64, i64) -> i64
    "llvm.call"(%12, %36, %39) <{CConv = #llvm.cconv<fastcc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.nonnull, llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @fd_sha512_core_ref, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.br"()[^bb8] : () -> ()
  ^bb8:  // 2 preds: ^bb6, ^bb7
    %40 = "llvm.and"(%37, %9) : (i64, i64) -> i64
    %41 = "llvm.icmp"(%40, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%41)[^bb10, ^bb9] <{branch_weights = array<i32: 2000, 1>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb9:  // pred: ^bb8
    %42 = "llvm.and"(%37, %10) : (i64, i64) -> i64
    %43 = "llvm.getelementptr"(%36, %42) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%arg0, %43, %40) <{alias_scopes = [#alias_scope4, #alias_scope5], arg_attrs = [{llvm.align = 1 : i64}, {llvm.align = 1 : i64, llvm.readonly}, {}], isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.store"(%40, %13) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    "llvm.br"()[^bb10] : () -> ()
  ^bb10:  // 4 preds: ^bb0, ^bb5, ^bb8, ^bb9
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
  }) : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<fastcc>, arg_attrs = [{llvm.nocapture, llvm.noundef}, {llvm.nocapture, llvm.noundef, llvm.readonly}, {llvm.noundef, llvm.range = #llvm.constant_range<i64, 1, 144115188075855872>}], dso_local, function_type = !llvm.func<void (ptr, ptr, i64)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["nofree", "norecurse", "nosync", ["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], sym_name = "fd_sha512_core_ref", target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 1 : i64}> ({
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "Ubuntu clang version 21.1.8 (6ubuntu1)", llvm.module_asm = [], llvm.target_triple = "x86_64-pc-linux-gnu"} : () -> ()

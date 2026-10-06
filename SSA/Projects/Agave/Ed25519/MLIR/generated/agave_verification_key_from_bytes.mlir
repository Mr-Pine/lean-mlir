"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 168 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.noundef, llvm.sret = !llvm.array<168 x i8>, llvm.writeonly}, {llvm.dereferenceable = 32 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.noundef, llvm.readonly}], function_type = !llvm.func<void (ptr, ptr)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["nofree", "norecurse", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], sym_name = "_RNvMs2_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_18CompressedEdwardsY10decompress", target_cpu = "x86-64", unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64}> ({
  }) : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 200 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.noundef, llvm.sret = !llvm.array<200 x i8>, llvm.writeonly}, {llvm.align = 1 : i64, llvm.dereferenceable = 32 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.noundef, llvm.readonly}], function_type = !llvm.func<void (ptr, ptr)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["nofree", "norecurse", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], sym_name = "_RNvXs8_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKeyINtNtCsgxBkk5gSRhY_4core7convert7TryFromNtB5_20VerificationKeyBytesE8try_from", target_cpu = "x86-64", unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64}> ({
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %3 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 48 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 80 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 88 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 120 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 128 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 136 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 152 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = dense<[36028797018963664, 36028797018963952]> : vector<2xi64>}> : () -> vector<2xi64>
    %15 = "llvm.mlir.constant"() <{value = dense<36028797018963952> : vector<2xi64>}> : () -> vector<2xi64>
    %16 = "llvm.mlir.constant"() <{value = dense<51> : vector<2xi64>}> : () -> vector<2xi64>
    %17 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %18 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %19 = "llvm.mlir.constant"() <{value = dense<2251799813685247> : vector<2xi64>}> : () -> vector<2xi64>
    %20 = "llvm.mlir.constant"() <{value = 64 : i64}> : () -> i64
    %21 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %22 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %23 = "llvm.mlir.constant"() <{value = 160 : i64}> : () -> i64
    %24 = "llvm.mlir.constant"() <{value = 168 : i64}> : () -> i64
    %25 = "llvm.mlir.constant"() <{value = 184 : i64}> : () -> i64
    %26 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %27 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<168 x i8>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%27) : (!llvm.ptr) -> ()
    "llvm.call"(%27, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 168 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<168 x i8>}, {llvm.dereferenceable = 32 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvMs2_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_18CompressedEdwardsY10decompress, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (!llvm.ptr, !llvm.ptr) -> ()
    %28 = "llvm.load"(%27) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %29 = "llvm.trunc"(%28) <{overflowFlags = 2 : i32}> : (i64) -> i1
    "llvm.cond_br"(%29)[^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:  // pred: ^bb0
    %30 = "llvm.getelementptr"(%27, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %31 = "llvm.getelementptr"(%27, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %32 = "llvm.getelementptr"(%27, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %33 = "llvm.getelementptr"(%27, %6) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %34 = "llvm.getelementptr"(%arg0, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%34, %33, %8) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %35 = "llvm.getelementptr"(%27, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %36 = "llvm.getelementptr"(%arg0, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%36, %35, %8) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %37 = "llvm.getelementptr"(%27, %11) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %38 = "llvm.getelementptr"(%27, %12) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %39 = "llvm.getelementptr"(%27, %13) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %40 = "llvm.getelementptr"(%arg0, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %41 = "llvm.getelementptr"(%arg0, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %42 = "llvm.getelementptr"(%arg0, %6) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %43 = "llvm.load"(%30) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
    %44 = "llvm.load"(%31) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
    %45 = "llvm.sub"(%14, %43) <{overflowFlags = 0 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %46 = "llvm.sub"(%15, %44) <{overflowFlags = 0 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %47 = "llvm.lshr"(%45, %16) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %48 = "llvm.extractelement"(%45, %17) : (vector<2xi64>, i64) -> i64
    %49 = "llvm.and"(%48, %18) : (i64, i64) -> i64
    %50 = "llvm.and"(%46, %19) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %51 = "llvm.add"(%50, %47) <{overflowFlags = 3 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %52 = "llvm.getelementptr"(%arg0, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %53 = "llvm.load"(%32) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
    %54 = "llvm.sub"(%15, %53) <{overflowFlags = 0 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %55 = "llvm.extractelement"(%54, %1) : (vector<2xi64>, i64) -> i64
    %56 = "llvm.lshr"(%55, %21) : (i64, i64) -> i64
    %57 = "llvm.and"(%54, %19) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %58 = "llvm.mul"(%56, %22) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %59 = "llvm.shufflevector"(%46, %54) <{mask = array<i32: 1, 2>}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %60 = "llvm.lshr"(%59, %16) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %61 = "llvm.add"(%58, %49) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %62 = "llvm.add"(%57, %60) <{overflowFlags = 3 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %63 = "llvm.getelementptr"(%arg0, %23) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %64 = "llvm.getelementptr"(%arg0, %24) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %65 = "llvm.load"(%37) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
    %66 = "llvm.load"(%38) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
    %67 = "llvm.sub"(%14, %65) <{overflowFlags = 0 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %68 = "llvm.sub"(%15, %66) <{overflowFlags = 0 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %69 = "llvm.lshr"(%67, %16) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %70 = "llvm.extractelement"(%67, %17) : (vector<2xi64>, i64) -> i64
    %71 = "llvm.and"(%70, %18) : (i64, i64) -> i64
    %72 = "llvm.and"(%68, %19) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %73 = "llvm.add"(%72, %69) <{overflowFlags = 3 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %74 = "llvm.getelementptr"(%arg0, %25) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %75 = "llvm.load"(%39) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
    %76 = "llvm.sub"(%15, %75) <{overflowFlags = 0 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %77 = "llvm.extractelement"(%76, %1) : (vector<2xi64>, i64) -> i64
    %78 = "llvm.lshr"(%77, %21) : (i64, i64) -> i64
    %79 = "llvm.and"(%76, %19) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %80 = "llvm.mul"(%78, %22) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %81 = "llvm.shufflevector"(%68, %76) <{mask = array<i32: 1, 2>}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %82 = "llvm.lshr"(%81, %16) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %83 = "llvm.add"(%80, %71) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %84 = "llvm.add"(%79, %82) <{overflowFlags = 3 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    "llvm.intr.lifetime.end"(%27) : (!llvm.ptr) -> ()
    "llvm.intr.memcpy"(%40, %arg1, %5) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 1 : i64, llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.store"(%61, %41) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%51, %42) <{alignment = 8 : i64, ordering = 0 : i64}> : (vector<2xi64>, !llvm.ptr) -> ()
    "llvm.store"(%62, %52) <{alignment = 8 : i64, ordering = 0 : i64}> : (vector<2xi64>, !llvm.ptr) -> ()
    "llvm.store"(%83, %63) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%73, %64) <{alignment = 8 : i64, ordering = 0 : i64}> : (vector<2xi64>, !llvm.ptr) -> ()
    "llvm.store"(%84, %74) <{alignment = 8 : i64, ordering = 0 : i64}> : (vector<2xi64>, !llvm.ptr) -> ()
    "llvm.br"(%26)[^bb3] : (i8) -> ()
  ^bb2:  // pred: ^bb0
    "llvm.intr.lifetime.end"(%27) : (!llvm.ptr) -> ()
    %85 = "llvm.getelementptr"(%arg0, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%2, %85) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    "llvm.br"(%2)[^bb3] : (i8) -> ()
  ^bb3(%86: i8):  // 2 preds: ^bb1, ^bb2
    "llvm.store"(%86, %arg0) <{alignment = 8 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

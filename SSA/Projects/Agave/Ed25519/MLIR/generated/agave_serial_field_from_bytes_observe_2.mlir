#alias_scope_domain = #llvm.alias_scope_domain<id = distinct[0]<>, description = "_RINvNtCsgxBkk5gSRhY_4core5slice20copy_from_slice_implhECsjK63O35OHGN_14solana_ed25519">
#alias_scope_domain1 = #llvm.alias_scope_domain<id = distinct[1]<>, description = "_RINvNtCsgxBkk5gSRhY_4core5slice20copy_from_slice_implhECsjK63O35OHGN_14solana_ed25519">
#alias_scope_domain2 = #llvm.alias_scope_domain<id = distinct[2]<>, description = "_RNvNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB7_14FieldElement5110from_bytes8load8_at">
#alias_scope_domain3 = #llvm.alias_scope_domain<id = distinct[3]<>, description = "_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement5110from_bytes">
#alias_scope = #llvm.alias_scope<id = distinct[4]<>, domain = #alias_scope_domain, description = "_RINvNtCsgxBkk5gSRhY_4core5slice20copy_from_slice_implhECsjK63O35OHGN_14solana_ed25519: %dest.0">
#alias_scope1 = #llvm.alias_scope<id = distinct[5]<>, domain = #alias_scope_domain, description = "_RINvNtCsgxBkk5gSRhY_4core5slice20copy_from_slice_implhECsjK63O35OHGN_14solana_ed25519: %src.0">
#alias_scope2 = #llvm.alias_scope<id = distinct[6]<>, domain = #alias_scope_domain, description = "_RINvNtCsgxBkk5gSRhY_4core5slice20copy_from_slice_implhECsjK63O35OHGN_14solana_ed25519: argument 2">
#alias_scope3 = #llvm.alias_scope<id = distinct[7]<>, domain = #alias_scope_domain1, description = "_RINvNtCsgxBkk5gSRhY_4core5slice20copy_from_slice_implhECsjK63O35OHGN_14solana_ed25519: %dest.0">
#alias_scope4 = #llvm.alias_scope<id = distinct[8]<>, domain = #alias_scope_domain1, description = "_RINvNtCsgxBkk5gSRhY_4core5slice20copy_from_slice_implhECsjK63O35OHGN_14solana_ed25519: %src.0">
#alias_scope5 = #llvm.alias_scope<id = distinct[9]<>, domain = #alias_scope_domain1, description = "_RINvNtCsgxBkk5gSRhY_4core5slice20copy_from_slice_implhECsjK63O35OHGN_14solana_ed25519: argument 2">
#alias_scope6 = #llvm.alias_scope<id = distinct[10]<>, domain = #alias_scope_domain2, description = "_RNvNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB7_14FieldElement5110from_bytes8load8_at: %input.0">
#alias_scope7 = #llvm.alias_scope<id = distinct[11]<>, domain = #alias_scope_domain3, description = "_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement5110from_bytes: %bytes">
#alias_scope8 = #llvm.alias_scope<id = distinct[12]<>, domain = #alias_scope_domain3, description = "_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement5110from_bytes: %_0">
"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}], function_type = !llvm.func<i64 (i64, i64, i64, i64)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], res_attrs = [{llvm.noundef, llvm.range = #llvm.constant_range<i64, 0, 2251799813685248>}], sym_name = "agave_serial_field_from_bytes_observe_2", target_cpu = "x86-64", unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
  ^bb0(%arg0: i64, %arg1: i64, %arg2: i64, %arg3: i64):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %5 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<16 x i8>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%5) : (!llvm.ptr) -> ()
    "llvm.store"(%arg1, %5) <{alias_scopes = [#alias_scope, #alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope2], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %6 = "llvm.getelementptr"(%5, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%arg2, %6) <{alias_scopes = [#alias_scope3, #alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope5], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %7 = "llvm.getelementptr"(%5, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %8 = "llvm.load"(%7) <{alias_scopes = [#alias_scope6, #alias_scope7], alignment = 4 : i64, noalias_scopes = [#alias_scope8], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %9 = "llvm.lshr"(%8, %3) : (i64, i64) -> i64
    %10 = "llvm.and"(%9, %4) : (i64, i64) -> i64
    "llvm.intr.lifetime.end"(%5) : (!llvm.ptr) -> ()
    "llvm.return"(%10) : (i64) -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

#tbaa_root = #llvm.tbaa_root<id = "Simple C/C++ TBAA">
#tbaa_type_desc = #llvm.tbaa_type_desc<id = "omnipotent char", members = {<#tbaa_root, 0>}>
#tbaa_type_desc1 = #llvm.tbaa_type_desc<id = "long", members = {<#tbaa_type_desc, 0>}>
#tbaa_tag = #llvm.tbaa_tag<base_type = #tbaa_type_desc1, access_type = #tbaa_type_desc1, offset = 0>
"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<error, "wchar_size", 4 : i32>, #llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<max, "PIE Level", 2 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.noundef, llvm.returned, llvm.writeonly}], dso_local, function_type = !llvm.func<ptr (ptr)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = write, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", ["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], res_attrs = [{llvm.noundef}], sym_name = "fd_sha512_init", target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", unnamed_addr = 1 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 128 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 7640891576956012808 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 136 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = -4942790177534073029 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 144 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 4354685564936845355 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 152 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = -6534734903238641935 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 160 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 5840696475078001361 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 168 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = -7276294671716946913 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 176 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 2270897969802886507 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = 184 : i64}> : () -> i64
    %15 = "llvm.mlir.constant"() <{value = 6620516959819538809 : i64}> : () -> i64
    %16 = "llvm.mlir.constant"() <{value = 200 : i64}> : () -> i64
    %17 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %18 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> i64
    %19 = "llvm.getelementptr"(%arg0, %0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%1, %19) <{alignment = 128 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    %20 = "llvm.getelementptr"(%arg0, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%3, %20) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    %21 = "llvm.getelementptr"(%arg0, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%5, %21) <{alignment = 16 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    %22 = "llvm.getelementptr"(%arg0, %6) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%7, %22) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    %23 = "llvm.getelementptr"(%arg0, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%9, %23) <{alignment = 32 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    %24 = "llvm.getelementptr"(%arg0, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%11, %24) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    %25 = "llvm.getelementptr"(%arg0, %12) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%13, %25) <{alignment = 16 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    %26 = "llvm.getelementptr"(%arg0, %14) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%15, %26) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (i64, !llvm.ptr) -> ()
    %27 = "llvm.getelementptr"(%arg0, %16) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memset"(%27, %17, %18) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}, {}, {}], isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "Ubuntu clang version 21.1.8 (6ubuntu1)", llvm.module_asm = [], llvm.target_triple = "x86_64-pc-linux-gnu"} : () -> ()

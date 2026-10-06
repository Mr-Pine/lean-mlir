"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}], function_type = !llvm.func<i64 (i64, i64, i64, i64, i64)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], res_attrs = [{llvm.noundef}], sym_name = "agave_serial_field_to_bytes_observe_0", target_cpu = "x86-64", unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
  ^bb0(%arg0: i64, %arg1: i64, %arg2: i64, %arg3: i64, %arg4: i64):
    %0 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %3 = "llvm.lshr"(%arg0, %0) : (i64, i64) -> i64
    %4 = "llvm.lshr"(%arg1, %0) : (i64, i64) -> i64
    %5 = "llvm.lshr"(%arg2, %0) : (i64, i64) -> i64
    %6 = "llvm.lshr"(%arg3, %0) : (i64, i64) -> i64
    %7 = "llvm.lshr"(%arg4, %0) : (i64, i64) -> i64
    %8 = "llvm.and"(%arg0, %1) : (i64, i64) -> i64
    %9 = "llvm.and"(%arg1, %1) : (i64, i64) -> i64
    %10 = "llvm.and"(%arg2, %1) : (i64, i64) -> i64
    %11 = "llvm.and"(%arg3, %1) : (i64, i64) -> i64
    %12 = "llvm.and"(%arg4, %1) : (i64, i64) -> i64
    %13 = "llvm.mul"(%7, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %14 = "llvm.add"(%13, %8) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %15 = "llvm.add"(%9, %3) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %16 = "llvm.add"(%10, %4) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %17 = "llvm.add"(%11, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %18 = "llvm.add"(%12, %6) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %19 = "llvm.add"(%14, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %20 = "llvm.lshr"(%19, %0) : (i64, i64) -> i64
    %21 = "llvm.add"(%20, %15) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %22 = "llvm.lshr"(%21, %0) : (i64, i64) -> i64
    %23 = "llvm.add"(%16, %22) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %24 = "llvm.lshr"(%23, %0) : (i64, i64) -> i64
    %25 = "llvm.add"(%17, %24) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %26 = "llvm.lshr"(%25, %0) : (i64, i64) -> i64
    %27 = "llvm.add"(%18, %26) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %28 = "llvm.lshr"(%27, %0) : (i64, i64) -> i64
    %29 = "llvm.mul"(%28, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %30 = "llvm.add"(%29, %14) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %31 = "llvm.shl"(%15, %0) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %32 = "llvm.add"(%30, %31) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    "llvm.return"(%32) : (i64) -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

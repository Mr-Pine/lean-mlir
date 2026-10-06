"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}], function_type = !llvm.func<i64 (i64, i64, i64, i64, i64)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], res_attrs = [{llvm.noundef}], sym_name = "agave_serial_field_to_bytes_observe_2", target_cpu = "x86-64", unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
  ^bb0(%arg0: i64, %arg1: i64, %arg2: i64, %arg3: i64, %arg4: i64):
    %0 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 50 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 25 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 254 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 255 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 16776960 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = -4294967296 : i64}> : () -> i64
    %12 = "llvm.lshr"(%arg0, %0) : (i64, i64) -> i64
    %13 = "llvm.lshr"(%arg1, %0) : (i64, i64) -> i64
    %14 = "llvm.lshr"(%arg2, %0) : (i64, i64) -> i64
    %15 = "llvm.lshr"(%arg3, %0) : (i64, i64) -> i64
    %16 = "llvm.lshr"(%arg4, %0) : (i64, i64) -> i64
    %17 = "llvm.and"(%arg0, %1) : (i64, i64) -> i64
    %18 = "llvm.and"(%arg1, %1) : (i64, i64) -> i64
    %19 = "llvm.and"(%arg2, %1) : (i64, i64) -> i64
    %20 = "llvm.and"(%arg3, %1) : (i64, i64) -> i64
    %21 = "llvm.and"(%arg4, %1) : (i64, i64) -> i64
    %22 = "llvm.mul"(%16, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %23 = "llvm.add"(%22, %17) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %24 = "llvm.add"(%18, %12) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %25 = "llvm.add"(%19, %13) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %26 = "llvm.add"(%20, %14) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %27 = "llvm.add"(%21, %15) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %28 = "llvm.add"(%23, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %29 = "llvm.lshr"(%28, %0) : (i64, i64) -> i64
    %30 = "llvm.add"(%29, %24) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %31 = "llvm.lshr"(%30, %0) : (i64, i64) -> i64
    %32 = "llvm.add"(%31, %25) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %33 = "llvm.lshr"(%32, %0) : (i64, i64) -> i64
    %34 = "llvm.add"(%33, %26) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %35 = "llvm.lshr"(%34, %0) : (i64, i64) -> i64
    %36 = "llvm.add"(%27, %35) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %37 = "llvm.lshr"(%36, %0) : (i64, i64) -> i64
    %38 = "llvm.mul"(%37, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %39 = "llvm.add"(%38, %23) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %40 = "llvm.lshr"(%39, %0) : (i64, i64) -> i64
    %41 = "llvm.add"(%40, %24) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %42 = "llvm.lshr"(%41, %0) : (i64, i64) -> i64
    %43 = "llvm.add"(%42, %25) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %44 = "llvm.lshr"(%43, %0) : (i64, i64) -> i64
    %45 = "llvm.add"(%44, %26) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %46 = "llvm.lshr"(%43, %3) : (i64, i64) -> i64
    %47 = "llvm.lshr"(%43, %4) : (i64, i64) -> i64
    %48 = "llvm.and"(%47, %5) : (i64, i64) -> i64
    %49 = "llvm.shl"(%45, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %50 = "llvm.shl"(%45, %6) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %51 = "llvm.and"(%49, %7) : (i64, i64) -> i64
    %52 = "llvm.or"(%51, %48) <{isDisjoint}> : (i64, i64) -> i64
    %53 = "llvm.shl"(%52, %8) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %54 = "llvm.and"(%46, %9) : (i64, i64) -> i64
    %55 = "llvm.and"(%46, %10) : (i64, i64) -> i64
    %56 = "llvm.and"(%50, %11) : (i64, i64) -> i64
    %57 = "llvm.or"(%55, %56) <{isDisjoint}> : (i64, i64) -> i64
    %58 = "llvm.or"(%57, %53) <{isDisjoint}> : (i64, i64) -> i64
    %59 = "llvm.or"(%58, %54) <{isDisjoint}> : (i64, i64) -> i64
    "llvm.return"(%59) : (i64) -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

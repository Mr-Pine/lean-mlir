"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}], function_type = !llvm.func<i64 (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], res_attrs = [{llvm.noundef}], sym_name = "agave_serial_field_mul_observe_3", target_cpu = "x86-64", unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
  ^bb0(%arg0: i64, %arg1: i64, %arg2: i64, %arg3: i64, %arg4: i64, %arg5: i64, %arg6: i64, %arg7: i64, %arg8: i64, %arg9: i64):
    %0 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 51 : i128}> : () -> i128
    %2 = "llvm.mlir.constant"() <{value = 18446744073709551615 : i128}> : () -> i128
    %3 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %4 = "llvm.mul"(%arg6, %0) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %5 = "llvm.mul"(%arg7, %0) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %6 = "llvm.mul"(%arg8, %0) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %7 = "llvm.mul"(%arg9, %0) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %8 = "llvm.zext"(%arg0) : (i64) -> i128
    %9 = "llvm.zext"(%arg5) : (i64) -> i128
    %10 = "llvm.mul"(%9, %8) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %11 = "llvm.zext"(%arg4) : (i64) -> i128
    %12 = "llvm.zext"(%4) : (i64) -> i128
    %13 = "llvm.mul"(%11, %12) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %14 = "llvm.add"(%13, %10) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %15 = "llvm.zext"(%arg3) : (i64) -> i128
    %16 = "llvm.zext"(%5) : (i64) -> i128
    %17 = "llvm.mul"(%15, %16) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %18 = "llvm.add"(%14, %17) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %19 = "llvm.zext"(%arg2) : (i64) -> i128
    %20 = "llvm.zext"(%6) : (i64) -> i128
    %21 = "llvm.mul"(%19, %20) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %22 = "llvm.add"(%18, %21) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %23 = "llvm.zext"(%arg1) : (i64) -> i128
    %24 = "llvm.zext"(%7) : (i64) -> i128
    %25 = "llvm.mul"(%23, %24) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %26 = "llvm.add"(%22, %25) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %27 = "llvm.mul"(%23, %9) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %28 = "llvm.zext"(%arg6) : (i64) -> i128
    %29 = "llvm.mul"(%8, %28) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %30 = "llvm.mul"(%11, %16) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %31 = "llvm.mul"(%15, %20) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %32 = "llvm.mul"(%19, %24) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %33 = "llvm.mul"(%19, %9) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %34 = "llvm.mul"(%23, %28) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %35 = "llvm.zext"(%arg7) : (i64) -> i128
    %36 = "llvm.mul"(%8, %35) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %37 = "llvm.mul"(%11, %20) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %38 = "llvm.mul"(%15, %24) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %39 = "llvm.mul"(%15, %9) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %40 = "llvm.mul"(%19, %28) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %41 = "llvm.mul"(%23, %35) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %42 = "llvm.zext"(%arg8) : (i64) -> i128
    %43 = "llvm.mul"(%8, %42) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %44 = "llvm.mul"(%11, %24) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %45 = "llvm.lshr"(%26, %1) : (i128, i128) -> i128
    %46 = "llvm.and"(%45, %2) : (i128, i128) -> i128
    %47 = "llvm.add"(%30, %29) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %48 = "llvm.add"(%47, %31) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %49 = "llvm.add"(%48, %32) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %50 = "llvm.add"(%49, %27) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %51 = "llvm.add"(%50, %46) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %52 = "llvm.lshr"(%51, %1) : (i128, i128) -> i128
    %53 = "llvm.and"(%52, %2) : (i128, i128) -> i128
    %54 = "llvm.add"(%37, %36) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %55 = "llvm.add"(%54, %38) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %56 = "llvm.add"(%55, %33) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %57 = "llvm.add"(%56, %34) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %58 = "llvm.add"(%57, %53) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %59 = "llvm.lshr"(%58, %1) : (i128, i128) -> i128
    %60 = "llvm.add"(%44, %43) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %61 = "llvm.add"(%60, %39) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %62 = "llvm.add"(%61, %40) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %63 = "llvm.add"(%62, %41) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %64 = "llvm.add"(%63, %59) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %65 = "llvm.trunc"(%64) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %66 = "llvm.and"(%65, %3) : (i64, i64) -> i64
    "llvm.return"(%66) : (i64) -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

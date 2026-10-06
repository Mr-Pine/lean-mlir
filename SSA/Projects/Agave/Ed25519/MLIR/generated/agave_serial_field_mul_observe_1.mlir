"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}], function_type = !llvm.func<i64 (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], res_attrs = [{llvm.noundef}], sym_name = "agave_serial_field_mul_observe_1", target_cpu = "x86-64", unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
  ^bb0(%arg0: i64, %arg1: i64, %arg2: i64, %arg3: i64, %arg4: i64, %arg5: i64, %arg6: i64, %arg7: i64, %arg8: i64, %arg9: i64):
    %0 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 51 : i128}> : () -> i128
    %2 = "llvm.mlir.constant"() <{value = 18446744073709551615 : i128}> : () -> i128
    %3 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %5 = "llvm.mul"(%arg6, %0) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %6 = "llvm.mul"(%arg7, %0) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %7 = "llvm.mul"(%arg8, %0) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %8 = "llvm.mul"(%arg9, %0) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %9 = "llvm.zext"(%arg0) : (i64) -> i128
    %10 = "llvm.zext"(%arg5) : (i64) -> i128
    %11 = "llvm.mul"(%10, %9) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %12 = "llvm.zext"(%arg4) : (i64) -> i128
    %13 = "llvm.zext"(%5) : (i64) -> i128
    %14 = "llvm.mul"(%12, %13) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %15 = "llvm.add"(%14, %11) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %16 = "llvm.zext"(%arg3) : (i64) -> i128
    %17 = "llvm.zext"(%6) : (i64) -> i128
    %18 = "llvm.mul"(%16, %17) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %19 = "llvm.add"(%15, %18) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %20 = "llvm.zext"(%arg2) : (i64) -> i128
    %21 = "llvm.zext"(%7) : (i64) -> i128
    %22 = "llvm.mul"(%20, %21) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %23 = "llvm.add"(%19, %22) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %24 = "llvm.zext"(%arg1) : (i64) -> i128
    %25 = "llvm.zext"(%8) : (i64) -> i128
    %26 = "llvm.mul"(%24, %25) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %27 = "llvm.add"(%23, %26) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %28 = "llvm.mul"(%24, %10) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %29 = "llvm.zext"(%arg6) : (i64) -> i128
    %30 = "llvm.mul"(%9, %29) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %31 = "llvm.mul"(%12, %17) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %32 = "llvm.mul"(%16, %21) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %33 = "llvm.mul"(%20, %25) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %34 = "llvm.mul"(%20, %10) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %35 = "llvm.mul"(%24, %29) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %36 = "llvm.zext"(%arg7) : (i64) -> i128
    %37 = "llvm.mul"(%9, %36) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %38 = "llvm.mul"(%12, %21) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %39 = "llvm.mul"(%16, %25) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %40 = "llvm.mul"(%16, %10) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %41 = "llvm.mul"(%20, %29) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %42 = "llvm.mul"(%24, %36) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %43 = "llvm.zext"(%arg8) : (i64) -> i128
    %44 = "llvm.mul"(%9, %43) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %45 = "llvm.mul"(%12, %25) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %46 = "llvm.mul"(%12, %10) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %47 = "llvm.mul"(%16, %29) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %48 = "llvm.mul"(%20, %36) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %49 = "llvm.mul"(%24, %43) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %50 = "llvm.zext"(%arg9) : (i64) -> i128
    %51 = "llvm.mul"(%9, %50) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %52 = "llvm.lshr"(%27, %1) : (i128, i128) -> i128
    %53 = "llvm.and"(%52, %2) : (i128, i128) -> i128
    %54 = "llvm.add"(%31, %30) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %55 = "llvm.add"(%54, %32) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %56 = "llvm.add"(%55, %33) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %57 = "llvm.add"(%56, %28) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %58 = "llvm.add"(%57, %53) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %59 = "llvm.trunc"(%27) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %60 = "llvm.and"(%59, %3) : (i64, i64) -> i64
    %61 = "llvm.lshr"(%58, %1) : (i128, i128) -> i128
    %62 = "llvm.and"(%61, %2) : (i128, i128) -> i128
    %63 = "llvm.add"(%38, %37) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %64 = "llvm.add"(%63, %39) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %65 = "llvm.add"(%64, %34) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %66 = "llvm.add"(%65, %35) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %67 = "llvm.add"(%66, %62) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %68 = "llvm.trunc"(%58) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %69 = "llvm.and"(%68, %3) : (i64, i64) -> i64
    %70 = "llvm.lshr"(%67, %1) : (i128, i128) -> i128
    %71 = "llvm.and"(%70, %2) : (i128, i128) -> i128
    %72 = "llvm.add"(%45, %44) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %73 = "llvm.add"(%72, %40) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %74 = "llvm.add"(%73, %41) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %75 = "llvm.add"(%74, %42) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %76 = "llvm.add"(%75, %71) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %77 = "llvm.lshr"(%76, %1) : (i128, i128) -> i128
    %78 = "llvm.and"(%77, %2) : (i128, i128) -> i128
    %79 = "llvm.add"(%46, %51) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %80 = "llvm.add"(%79, %47) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %81 = "llvm.add"(%80, %48) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %82 = "llvm.add"(%81, %49) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %83 = "llvm.add"(%82, %78) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %84 = "llvm.lshr"(%83, %1) : (i128, i128) -> i128
    %85 = "llvm.trunc"(%84) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %86 = "llvm.mul"(%85, %0) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %87 = "llvm.add"(%86, %60) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %88 = "llvm.lshr"(%87, %4) : (i64, i64) -> i64
    %89 = "llvm.add"(%88, %69) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.return"(%89) : (i64) -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

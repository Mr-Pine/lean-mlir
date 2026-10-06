"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<vector<4xi64> (vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], sym_name = "agave_avx2_field_reduce_observe_0", target_cpu = "x86-64", target_features = #llvm.target_features<["+avx", "+avx2", "+sse", "+sse2", "+sse3", "+sse4.1", "+sse4.2", "+crc32", "+ssse3"]>, unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = dense<[26, 26, 25, 25, 26, 26, 25, 25]> : vector<8xi32>}> : () -> vector<8xi32>
    %1 = "llvm.mlir.poison"() : () -> i32
    %2 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %3 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %4 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %5 = "llvm.insertelement"(%3, %2, %4) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %6 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %7 = "llvm.insertelement"(%5, %2, %6) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %8 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %9 = "llvm.insertelement"(%7, %1, %8) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %10 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %11 = "llvm.insertelement"(%9, %1, %10) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %12 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %13 = "llvm.insertelement"(%11, %2, %12) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %14 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %15 = "llvm.insertelement"(%13, %2, %14) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %16 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %17 = "llvm.insertelement"(%15, %1, %16) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %18 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %19 = "llvm.insertelement"(%17, %1, %18) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %20 = "llvm.mlir.constant"() <{value = dense<[67108863, 67108863, 33554431, 33554431, 67108863, 67108863, 33554431, 33554431]> : vector<8xi32>}> : () -> vector<8xi32>
    %21 = "llvm.mlir.constant"() <{value = dense<[0, 0, 127, 127, 0, 0, 127, 127]> : vector<8xi32>}> : () -> vector<8xi32>
    %22 = "llvm.mlir.poison"() : () -> vector<8xi32>
    %23 = "llvm.mlir.constant"() <{value = dense<19> : vector<4xi64>}> : () -> vector<4xi64>
    %24 = "llvm.bitcast"(%arg0) : (vector<4xi64>) -> vector<8xi32>
    %25 = "llvm.bitcast"(%arg4) : (vector<4xi64>) -> vector<8xi32>
    %26 = "llvm.lshr"(%24, %0) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %27 = "llvm.shufflevector"(%19, %26) <{mask = array<i32: 0, 1, 8, 9, 4, 5, 12, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %28 = "llvm.bitcast"(%arg0) : (vector<4xi64>) -> vector<8xi32>
    %29 = "llvm.and"(%28, %20) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %30 = "llvm.add"(%27, %29) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %31 = "llvm.lshr"(%25, %0) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %32 = "llvm.and"(%31, %21) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %33 = "llvm.shufflevector"(%32, %22) <{mask = array<i32: 2, 0, 3, 1, 6, 4, 7, 5>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %34 = "llvm.bitcast"(%33) : (vector<8xi32>) -> vector<4xi64>
    %35 = "llvm.mul"(%34, %23) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %36 = "llvm.bitcast"(%35) : (vector<4xi64>) -> vector<8xi32>
    %37 = "llvm.shufflevector"(%36, %22) <{mask = array<i32: 0, 2, 1, 3, 4, 6, 5, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %38 = "llvm.add"(%30, %37) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %39 = "llvm.bitcast"(%38) : (vector<8xi32>) -> vector<4xi64>
    "llvm.return"(%39) : (vector<4xi64>) -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

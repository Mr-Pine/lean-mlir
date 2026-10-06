"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<vector<4xi64> (vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], sym_name = "agave_avx2_field_reduce64_observe_2", target_cpu = "x86-64", target_features = #llvm.target_features<["+avx", "+avx2", "+sse", "+sse2", "+sse3", "+sse4.1", "+sse4.2", "+crc32", "+ssse3"]>, unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>, %arg5: vector<4xi64>, %arg6: vector<4xi64>, %arg7: vector<4xi64>, %arg8: vector<4xi64>, %arg9: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = dense<26> : vector<4xi64>}> : () -> vector<4xi64>
    %1 = "llvm.mlir.constant"() <{value = dense<67108863> : vector<4xi64>}> : () -> vector<4xi64>
    %2 = "llvm.mlir.constant"() <{value = dense<25> : vector<4xi64>}> : () -> vector<4xi64>
    %3 = "llvm.mlir.constant"() <{value = dense<33554431> : vector<4xi64>}> : () -> vector<4xi64>
    %4 = "llvm.mlir.poison"() : () -> i32
    %5 = "llvm.mlir.constant"() <{value = 67108863 : i32}> : () -> i32
    %6 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %7 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %8 = "llvm.insertelement"(%6, %5, %7) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %9 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %10 = "llvm.insertelement"(%8, %4, %9) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %11 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %12 = "llvm.insertelement"(%10, %5, %11) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %13 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %14 = "llvm.insertelement"(%12, %4, %13) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %15 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %16 = "llvm.insertelement"(%14, %5, %15) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %17 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %18 = "llvm.insertelement"(%16, %4, %17) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %19 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %20 = "llvm.insertelement"(%18, %5, %19) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %21 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %22 = "llvm.insertelement"(%20, %4, %21) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %23 = "llvm.lshr"(%arg0, %0) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %24 = "llvm.add"(%arg1, %23) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %25 = "llvm.lshr"(%arg4, %0) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %26 = "llvm.add"(%arg5, %25) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %27 = "llvm.and"(%arg4, %1) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %28 = "llvm.lshr"(%24, %2) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %29 = "llvm.add"(%28, %arg2) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %30 = "llvm.and"(%26, %3) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %31 = "llvm.lshr"(%29, %0) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %32 = "llvm.add"(%31, %arg3) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %33 = "llvm.lshr"(%32, %2) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %34 = "llvm.add"(%33, %27) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %35 = "llvm.lshr"(%34, %0) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %36 = "llvm.add"(%35, %30) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %37 = "llvm.bitcast"(%36) : (vector<4xi64>) -> vector<8xi32>
    %38 = "llvm.bitcast"(%34) : (vector<4xi64>) -> vector<8xi32>
    %39 = "llvm.and"(%38, %22) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %40 = "llvm.shufflevector"(%39, %37) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %41 = "llvm.bitcast"(%40) : (vector<8xi32>) -> vector<4xi64>
    "llvm.return"(%41) : (vector<4xi64>) -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

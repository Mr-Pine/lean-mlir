"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<warning, "RtLibUseGOT", 1 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<vector<4xi64> (vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>, vector<4xi64>)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "nonlazybind", ["probe-stack", "inline-asm"], ["target-cpu", "x86-64"]], sym_name = "agave_avx2_field_reduce_observe_4", target_cpu = "x86-64", target_features = #llvm.target_features<["+avx", "+avx2", "+sse", "+sse2", "+sse3", "+sse4.1", "+sse4.2", "+crc32", "+ssse3"]>, unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = dense<[25, 25, 26, 26, 25, 25, 26, 26]> : vector<8xi32>}> : () -> vector<8xi32>
    %1 = "llvm.mlir.constant"() <{value = dense<[67108863, 67108863, 33554431, 33554431, 67108863, 67108863, 33554431, 33554431]> : vector<8xi32>}> : () -> vector<8xi32>
    %2 = "llvm.shufflevector"(%arg3, %arg4) <{mask = array<i32: 1, 4, 3, 6>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %3 = "llvm.bitcast"(%2) : (vector<4xi64>) -> vector<8xi32>
    %4 = "llvm.lshr"(%3, %0) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %5 = "llvm.bitcast"(%arg4) : (vector<4xi64>) -> vector<8xi32>
    %6 = "llvm.and"(%5, %1) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %7 = "llvm.add"(%4, %6) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %8 = "llvm.bitcast"(%7) : (vector<8xi32>) -> vector<4xi64>
    "llvm.return"(%8) : (vector<4xi64>) -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "rustc version 1.98.1 (48a229cea 2026-09-01)", llvm.module_asm = [], llvm.target_triple = "x86_64-unknown-linux-gnu"} : () -> ()

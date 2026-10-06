module

public import SSA.Projects.RIR.Syntax.Elab
public import SSA.Projects.RIR.Run.Tactic
public import SSA.Projects.RIR.Run.Vector

namespace Agave.Ed25519.Reduce
open LeanMLIR.RIR
@[expose] public section

mlir_def observe0 :=
{
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
}

mlir_def observe1 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = dense<[25, 25, 26, 26, 25, 25, 26, 26]> : vector<8xi32>}> : () -> vector<8xi32>
    %1 = "llvm.mlir.constant"() <{value = dense<[67108863, 67108863, 33554431, 33554431, 67108863, 67108863, 33554431, 33554431]> : vector<8xi32>}> : () -> vector<8xi32>
    %2 = "llvm.shufflevector"(%arg0, %arg1) <{mask = array<i32: 1, 4, 3, 6>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %3 = "llvm.bitcast"(%2) : (vector<4xi64>) -> vector<8xi32>
    %4 = "llvm.lshr"(%3, %0) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %5 = "llvm.bitcast"(%arg1) : (vector<4xi64>) -> vector<8xi32>
    %6 = "llvm.and"(%5, %1) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %7 = "llvm.add"(%4, %6) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %8 = "llvm.bitcast"(%7) : (vector<8xi32>) -> vector<4xi64>
    "llvm.return"(%8) : (vector<4xi64>) -> ()
}

mlir_def observe2 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = dense<[25, 25, 26, 26, 25, 25, 26, 26]> : vector<8xi32>}> : () -> vector<8xi32>
    %1 = "llvm.mlir.constant"() <{value = dense<[67108863, 67108863, 33554431, 33554431, 67108863, 67108863, 33554431, 33554431]> : vector<8xi32>}> : () -> vector<8xi32>
    %2 = "llvm.shufflevector"(%arg1, %arg2) <{mask = array<i32: 1, 4, 3, 6>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %3 = "llvm.bitcast"(%2) : (vector<4xi64>) -> vector<8xi32>
    %4 = "llvm.lshr"(%3, %0) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %5 = "llvm.bitcast"(%arg2) : (vector<4xi64>) -> vector<8xi32>
    %6 = "llvm.and"(%5, %1) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %7 = "llvm.add"(%4, %6) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %8 = "llvm.bitcast"(%7) : (vector<8xi32>) -> vector<4xi64>
    "llvm.return"(%8) : (vector<4xi64>) -> ()
}

mlir_def observe3 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = dense<[25, 25, 26, 26, 25, 25, 26, 26]> : vector<8xi32>}> : () -> vector<8xi32>
    %1 = "llvm.mlir.constant"() <{value = dense<[67108863, 67108863, 33554431, 33554431, 67108863, 67108863, 33554431, 33554431]> : vector<8xi32>}> : () -> vector<8xi32>
    %2 = "llvm.shufflevector"(%arg2, %arg3) <{mask = array<i32: 1, 4, 3, 6>}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %3 = "llvm.bitcast"(%2) : (vector<4xi64>) -> vector<8xi32>
    %4 = "llvm.lshr"(%3, %0) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %5 = "llvm.bitcast"(%arg3) : (vector<4xi64>) -> vector<8xi32>
    %6 = "llvm.and"(%5, %1) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %7 = "llvm.add"(%4, %6) <{overflowFlags = 3 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %8 = "llvm.bitcast"(%7) : (vector<8xi32>) -> vector<4xi64>
    "llvm.return"(%8) : (vector<4xi64>) -> ()
}

mlir_def observe4 :=
{
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
}

end
end Agave.Ed25519.Reduce

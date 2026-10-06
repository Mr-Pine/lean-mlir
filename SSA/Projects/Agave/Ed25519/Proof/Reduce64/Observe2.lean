module
public import SSA.Projects.RIR.Syntax.Elab
/-! Exact compiler-generated region observing packed output register 2.
See the extraction manifest for the wrapper and optimization pipeline. -/
namespace Agave.Ed25519.Reduce64
@[expose] public section
mlir_def observe2 :=
{
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
}
end
end Agave.Ed25519.Reduce64

module
public import SSA.Projects.RIR.Syntax.Elab
/-! Exact compiler-generated region observing packed output register 4.
See the extraction manifest for the wrapper and optimization pipeline. -/
namespace Agave.Ed25519.Reduce64
@[expose] public section
mlir_def observe4 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>, %arg5: vector<4xi64>, %arg6: vector<4xi64>, %arg7: vector<4xi64>, %arg8: vector<4xi64>, %arg9: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = dense<26> : vector<4xi64>}> : () -> vector<4xi64>
    %1 = "llvm.mlir.constant"() <{value = dense<25> : vector<4xi64>}> : () -> vector<4xi64>
    %2 = "llvm.mlir.poison"() : () -> i32
    %3 = "llvm.mlir.constant"() <{value = 67108863 : i32}> : () -> i32
    %4 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %5 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %6 = "llvm.insertelement"(%4, %3, %5) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %7 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %8 = "llvm.insertelement"(%6, %2, %7) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %9 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %10 = "llvm.insertelement"(%8, %3, %9) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %11 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %12 = "llvm.insertelement"(%10, %2, %11) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %13 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %14 = "llvm.insertelement"(%12, %3, %13) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %15 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %16 = "llvm.insertelement"(%14, %2, %15) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %17 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %18 = "llvm.insertelement"(%16, %3, %17) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %19 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %20 = "llvm.insertelement"(%18, %2, %19) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %21 = "llvm.mlir.constant"() <{value = 33554431 : i32}> : () -> i32
    %22 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %23 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %24 = "llvm.insertelement"(%22, %21, %23) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %25 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %26 = "llvm.insertelement"(%24, %2, %25) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %27 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %28 = "llvm.insertelement"(%26, %21, %27) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %29 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %30 = "llvm.insertelement"(%28, %2, %29) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %31 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %32 = "llvm.insertelement"(%30, %21, %31) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %33 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %34 = "llvm.insertelement"(%32, %2, %33) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %35 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %36 = "llvm.insertelement"(%34, %21, %35) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %37 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %38 = "llvm.insertelement"(%36, %2, %37) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %39 = "llvm.lshr"(%arg4, %0) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %40 = "llvm.add"(%arg5, %39) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %41 = "llvm.lshr"(%40, %1) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %42 = "llvm.add"(%41, %arg6) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %43 = "llvm.lshr"(%42, %0) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %44 = "llvm.add"(%43, %arg7) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %45 = "llvm.lshr"(%44, %1) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %46 = "llvm.add"(%45, %arg8) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %47 = "llvm.lshr"(%46, %0) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %48 = "llvm.add"(%47, %arg9) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %49 = "llvm.bitcast"(%46) : (vector<4xi64>) -> vector<8xi32>
    %50 = "llvm.and"(%49, %20) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %51 = "llvm.bitcast"(%48) : (vector<4xi64>) -> vector<8xi32>
    %52 = "llvm.and"(%51, %38) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %53 = "llvm.shufflevector"(%50, %52) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %54 = "llvm.bitcast"(%53) : (vector<8xi32>) -> vector<4xi64>
    "llvm.return"(%54) : (vector<4xi64>) -> ()
}
end
end Agave.Ed25519.Reduce64

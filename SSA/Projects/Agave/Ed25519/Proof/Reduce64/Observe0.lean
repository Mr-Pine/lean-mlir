module
public import SSA.Projects.RIR.Syntax.Elab
/-! Exact compiler-generated region observing packed output register 0.
See the extraction manifest for the wrapper and optimization pipeline. -/
namespace Agave.Ed25519.Reduce64
@[expose] public section
mlir_def observe0 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>, %arg5: vector<4xi64>, %arg6: vector<4xi64>, %arg7: vector<4xi64>, %arg8: vector<4xi64>, %arg9: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = dense<26> : vector<4xi64>}> : () -> vector<4xi64>
    %1 = "llvm.mlir.constant"() <{value = dense<67108863> : vector<4xi64>}> : () -> vector<4xi64>
    %2 = "llvm.mlir.constant"() <{value = dense<33554431> : vector<4xi64>}> : () -> vector<4xi64>
    %3 = "llvm.mlir.constant"() <{value = dense<25> : vector<4xi64>}> : () -> vector<4xi64>
    %4 = "llvm.mlir.constant"() <{value = dense<51> : vector<4xi64>}> : () -> vector<4xi64>
    %5 = "llvm.mlir.constant"() <{value = dense<19> : vector<4xi64>}> : () -> vector<4xi64>
    %6 = "llvm.mlir.poison"() : () -> i32
    %7 = "llvm.mlir.constant"() <{value = 67108863 : i32}> : () -> i32
    %8 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %9 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %10 = "llvm.insertelement"(%8, %7, %9) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %11 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %12 = "llvm.insertelement"(%10, %6, %11) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %13 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %14 = "llvm.insertelement"(%12, %7, %13) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %15 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %16 = "llvm.insertelement"(%14, %6, %15) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %17 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %18 = "llvm.insertelement"(%16, %7, %17) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %19 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %20 = "llvm.insertelement"(%18, %6, %19) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %21 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %22 = "llvm.insertelement"(%20, %7, %21) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %23 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %24 = "llvm.insertelement"(%22, %6, %23) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %25 = "llvm.lshr"(%arg0, %0) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %26 = "llvm.add"(%arg1, %25) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %27 = "llvm.and"(%arg0, %1) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %28 = "llvm.lshr"(%arg4, %0) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %29 = "llvm.add"(%arg5, %28) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %30 = "llvm.and"(%26, %2) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %31 = "llvm.lshr"(%29, %3) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %32 = "llvm.add"(%31, %arg6) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %33 = "llvm.lshr"(%32, %0) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %34 = "llvm.add"(%33, %arg7) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %35 = "llvm.lshr"(%34, %3) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %36 = "llvm.add"(%35, %arg8) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %37 = "llvm.lshr"(%36, %0) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %38 = "llvm.add"(%37, %arg9) <{overflowFlags = 0 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %39 = "llvm.lshr"(%38, %3) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %40 = "llvm.and"(%39, %1) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %41 = "llvm.lshr"(%38, %4) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %42 = "llvm.mul"(%40, %5) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %43 = "llvm.mul"(%41, %5) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %44 = "llvm.add"(%42, %27) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %45 = "llvm.add"(%43, %30) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %46 = "llvm.lshr"(%44, %0) : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %47 = "llvm.add"(%45, %46) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %48 = "llvm.bitcast"(%44) : (vector<4xi64>) -> vector<8xi32>
    %49 = "llvm.and"(%48, %24) : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %50 = "llvm.bitcast"(%47) : (vector<4xi64>) -> vector<8xi32>
    %51 = "llvm.shufflevector"(%49, %50) <{mask = array<i32: 0, 2, 8, 10, 4, 6, 12, 14>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %52 = "llvm.bitcast"(%51) : (vector<8xi32>) -> vector<4xi64>
    "llvm.return"(%52) : (vector<4xi64>) -> ()
}
end
end Agave.Ed25519.Reduce64

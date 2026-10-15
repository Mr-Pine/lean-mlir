module

public import MLIR.Syntax.Elab

/-! # `dense<…>` constants: hex blobs and `i1` elements, as their list forms -/

namespace MLIR.Tests.Syntax.Dense

@[expose] public section

mlir_def hexVec := {
  ^bb0:
    %0 = "llvm.mlir.constant"() <{value = dense<"0x01000000FEFFFFFF"> : vector<2xi32>}> : () -> vector<2xi32>
    "llvm.return"(%0) : (vector<2xi32>) -> ()
}

mlir_def listVec := {
  ^bb0:
    %0 = "llvm.mlir.constant"() <{value = dense<[1, -2]> : vector<2xi32>}> : () -> vector<2xi32>
    "llvm.return"(%0) : (vector<2xi32>) -> ()
}

example : hexVec.entry.body = listVec.entry.body := rfl

mlir_def hexArray := {
  ^bb0:
    %0 = "llvm.mlir.constant"() <{value = dense<"0x0300000000000000FFFFFFFFFFFFFFFF"> : tensor<2xi64>}> : () -> !llvm.array<2 x i64>
    "llvm.return"(%0) : (!llvm.array<2 x i64>) -> ()
}

mlir_def listArray := {
  ^bb0:
    %0 = "llvm.mlir.constant"() <{value = dense<[3, -1]> : tensor<2xi64>}> : () -> !llvm.array<2 x i64>
    "llvm.return"(%0) : (!llvm.array<2 x i64>) -> ()
}

example : hexArray.entry.body = listArray.entry.body := rfl

-- `i1` elements: a byte each in hex, `true` and `false` in a list
mlir_def hexBits := {
  ^bb0:
    %0 = "llvm.mlir.constant"() <{value = dense<"0x00010001"> : vector<4xi1>}> : () -> vector<4xi1>
    "llvm.return"(%0) : (vector<4xi1>) -> ()
}

mlir_def boolBits := {
  ^bb0:
    %0 = "llvm.mlir.constant"() <{value = dense<[false, true, false, true]> : vector<4xi1>}> : () -> vector<4xi1>
    "llvm.return"(%0) : (vector<4xi1>) -> ()
}

mlir_def intBits := {
  ^bb0:
    %0 = "llvm.mlir.constant"() <{value = dense<[0, 1, 0, 1]> : vector<4xi1>}> : () -> vector<4xi1>
    "llvm.return"(%0) : (vector<4xi1>) -> ()
}

example : hexBits.entry.body = intBits.entry.body := rfl
example : boolBits.entry.body = intBits.entry.body := rfl

mlir_def splatTrue := {
  ^bb0:
    %0 = "llvm.mlir.constant"() <{value = dense<true> : vector<4xi1>}> : () -> vector<4xi1>
    "llvm.return"(%0) : (vector<4xi1>) -> ()
}

mlir_def splatOne := {
  ^bb0:
    %0 = "llvm.mlir.constant"() <{value = dense<1> : vector<4xi1>}> : () -> vector<4xi1>
    "llvm.return"(%0) : (vector<4xi1>) -> ()
}

example : splatTrue.entry.body = splatOne.entry.body := rfl

end

end MLIR.Tests.Syntax.Dense

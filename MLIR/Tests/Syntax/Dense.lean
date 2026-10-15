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

-- a long literal, `rir_vec%`'s: its elaboration and term are `log` deep
set_option maxRecDepth 128 in
noncomputable mlir_def longHex := {
  ^bb0:
    %0 = "llvm.mlir.constant"() <{value = dense<"0x000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F202122232425262728292A2B2C2D2E2F303132333435363738393A3B3C3D3E3F404142434445464748494A4B4C4D4E4F505152535455565758595A5B5C5D5E5F606162636465666768696A6B6C6D6E6F707172737475767778797A7B7C7D7E7F808182838485868788898A8B8C8D8E8F909192939495969798999A9B9C9D9E9FA0A1A2A3A4A5A6A7A8A9AAABACADAEAFB0B1B2B3B4B5B6B7B8B9BABBBCBDBEBFC0C1C2C3C4C5C6C7C8C9CACBCCCDCECFD0D1D2D3D4D5D6D7D8D9DADBDCDDDEDFE0E1E2E3E4E5E6E7E8E9EAEBECEDEEEFF0F1F2F3F4F5F6F7F8F9FAFBFCFDFEFF000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F202122232425262728292A2B2C2D2E2F303132333435363738393A3B3C3D3E3F404142434445464748494A4B4C4D4E4F505152535455565758595A5B5C5D5E5F606162636465666768696A6B6C6D6E6F707172737475767778797A7B7C7D7E7F808182838485868788898A8B8C8D8E8F909192939495969798999A9B9C9D9E9FA0A1A2A3A4A5A6A7A8A9AAABACADAEAFB0B1B2B3B4B5B6B7B8B9BABBBCBDBEBFC0C1C2C3C4C5C6C7C8C9CACBCCCDCECFD0D1D2D3D4D5D6D7D8D9DADBDCDDDEDFE0E1E2E3E4E5E6E7E8E9EAEBECEDEEEFF0F1F2F3F4F5F6F7F8F9FAFBFCFDFEFF000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F202122232425262728292A2B2C2D2E2F303132333435363738393A3B3C3D3E3F404142434445464748494A4B4C4D4E4F5051525354555657"> : vector<600xi8>}> : () -> vector<600xi8>
    "llvm.return"(%0) : (vector<600xi8>) -> ()
}

end

end MLIR.Tests.Syntax.Dense

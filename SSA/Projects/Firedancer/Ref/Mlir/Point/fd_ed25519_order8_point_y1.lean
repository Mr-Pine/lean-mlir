/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/ref/region/fd_ed25519_order8_point_y1.mlir
import SSA.Projects.SLLVM.Cfg

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fd_ed25519_order8_point_y1_region : MLIR.AST.Region 0 := [mlir_region|
{
    %0 = "llvm.mlir.constant"() <{value = dense<[84926274344903, 473620666599931, 365590438845504, 1028470286882429, 2146499180330972]> : tensor<5xi64>}> : () -> !llvm.array<5 x i64>
    %1 = "llvm.mlir.undef"() : () -> !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>
    %2 = "llvm.insertvalue"(%1, %0) <{position = array<i64: 0>}> : (!llvm.struct<"struct.fd_f25519", (array<5 x i64>)>, !llvm.array<5 x i64>) -> !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>
    %3 = "llvm.mlir.undef"() : () -> !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>
    %4 = "llvm.insertvalue"(%3, %2) <{position = array<i64: 0>}> : (!llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>) -> !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>
    "llvm.return"(%4) : (!llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>) -> ()
}
]

def fd_ed25519_order8_point_y1_init : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 320] :=
  [sllvm_of| fd_ed25519_order8_point_y1_region]

-- The limbs as the artifact writes them, packed little-endian by 64-bit lane --
-- the layout `LLVM.Ty.flattenBV` gives an aggregate. Pins the lift against the
-- artifact, so a spec may quote the constant without retyping it.
#guard InstCombine.LLVM.Ty.ofBitvec (fd_ed25519_order8_point_y1_init.denote Ctxt.Valuation.nil).head
    == .value (BitVec.ofNat 320 248547624636709978242923700447254355626407866746149546498081162889696353806486883190232979399)

end Firedancer.Ref

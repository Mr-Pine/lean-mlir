/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/ref/region/fd_ed25519_order8_point_y0.mlir
import SSA.Projects.SLLVM.Cfg

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fd_ed25519_order8_point_y0_region : MLIR.AST.Region 0 := [mlir_region|
{
    %0 = "llvm.mlir.constant"() <{value = dense<[2166873539340326, 1778179147085316, 1886209374839743, 1223329526802818, 105300633354275]> : tensor<5xi64>}> : () -> !llvm.array<5 x i64>
    %1 = "llvm.mlir.undef"() : () -> !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>
    %2 = "llvm.insertvalue"(%1, %0) <{position = array<i64: 0>}> : (!llvm.struct<"struct.fd_f25519", (array<5 x i64>)>, !llvm.array<5 x i64>) -> !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>
    %3 = "llvm.mlir.undef"() : () -> !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>
    %4 = "llvm.insertvalue"(%3, %2) <{position = array<i64: 0>}> : (!llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>) -> !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>
    "llvm.return"(%4) : (!llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>) -> ()
}
]

def fd_ed25519_order8_point_y0_init : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 320] :=
  [sllvm_of| fd_ed25519_order8_point_y0_region]

-- The limbs as the artifact writes them, packed little-endian by 64-bit lane --
-- the layout `LLVM.Ty.flattenBV` gives an aggregate. Pins the lift against the
-- artifact, so a spec may quote the constant without retyping it.
#guard InstCombine.LLVM.Ty.ofBitvec (fd_ed25519_order8_point_y0_init.denote Ctxt.Valuation.nil).head
    == .value (BitVec.ofNat 320 12192980334104125021482886871177693777525971344877968693128941921943918399272126260480174118)

end Firedancer.Ref

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/avx512/region/fd_ed25519_order8_point_y0.mlir
import SSA.Projects.SLLVM.Cfg

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_ed25519_order8_point_y0_region : MLIR.AST.Region 0 := [mlir_region|
{
    %0 = "llvm.mlir.constant"() <{value = dense<[3034655877158, 7251661554934, 8531478563367, 3751701540842, 152657171260, 51416324880, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %1 = "llvm.mlir.undef"() : () -> !llvm.struct<"struct.fd_f25519", (vector<8xi64>)>
    %2 = "llvm.insertvalue"(%1, %0) <{position = array<i64: 0>}> : (!llvm.struct<"struct.fd_f25519", (vector<8xi64>)>, vector<8xi64>) -> !llvm.struct<"struct.fd_f25519", (vector<8xi64>)>
    %3 = "llvm.mlir.undef"() : () -> !llvm.array<1 x struct<"struct.fd_f25519", (vector<8xi64>)>>
    %4 = "llvm.insertvalue"(%3, %2) <{position = array<i64: 0>}> : (!llvm.array<1 x struct<"struct.fd_f25519", (vector<8xi64>)>>, !llvm.struct<"struct.fd_f25519", (vector<8xi64>)>) -> !llvm.array<1 x struct<"struct.fd_f25519", (vector<8xi64>)>>
    "llvm.return"(%4) : (!llvm.array<1 x struct<"struct.fd_f25519", (vector<8xi64>)>>) -> ()
}
]

def fd_ed25519_order8_point_y0_init : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 512] :=
  [sllvm_of| fd_ed25519_order8_point_y0_region]

-- The limbs as the artifact writes them, packed little-endian by 64-bit lane --
-- the layout `LLVM.Ty.flattenBV` gives an aggregate. Pins the lift against the
-- artifact, so a spec may quote the constant without retyping it.
#guard InstCombine.LLVM.Ty.ofBitvec (fd_ed25519_order8_point_y0_init.denote Ctxt.Valuation.nil).head
    == .value (BitVec.ofNat 512 109824603378377742799366497336319773139601164200045246967266531110976483098768435934712383608117256877631526)

end Firedancer.Avx512

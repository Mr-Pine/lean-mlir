/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- build/native/gcc/mlir_canonicalized/avx512/region/fd_ed25519_order8_point_y1.mlir
import SSA.Projects.SLLVM.Cfg

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def fd_ed25519_order8_point_y1_region : MLIR.AST.Region 0 := [mlir_region|
{
    %0 = "llvm.mlir.constant"() <{value = dense<[5761437145031, 1544431467273, 264614458840, 5044391481365, 8643435850947, 1048095302895, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %1 = "llvm.mlir.undef"() : () -> !llvm.struct<"struct.fd_f25519", (vector<8xi64>)>
    %2 = "llvm.insertvalue"(%1, %0) <{position = array<i64: 0>}> : (!llvm.struct<"struct.fd_f25519", (vector<8xi64>)>, vector<8xi64>) -> !llvm.struct<"struct.fd_f25519", (vector<8xi64>)>
    %3 = "llvm.mlir.undef"() : () -> !llvm.array<1 x struct<"struct.fd_f25519", (vector<8xi64>)>>
    %4 = "llvm.insertvalue"(%3, %2) <{position = array<i64: 0>}> : (!llvm.array<1 x struct<"struct.fd_f25519", (vector<8xi64>)>>, !llvm.struct<"struct.fd_f25519", (vector<8xi64>)>) -> !llvm.array<1 x struct<"struct.fd_f25519", (vector<8xi64>)>>
    "llvm.return"(%4) : (!llvm.array<1 x struct<"struct.fd_f25519", (vector<8xi64>)>>) -> ()
}
]

def fd_ed25519_order8_point_y1_init : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 512] :=
  [sllvm_of| fd_ed25519_order8_point_y1_region]

-- The limbs as the artifact writes them, packed little-endian by 64-bit lane --
-- the layout `LLVM.Ty.flattenBV` gives an aggregate. Pins the lift against the
-- artifact, so a spec may quote the constant without retyping it.
#guard InstCombine.LLVM.Ty.ofBitvec (fd_ed25519_order8_point_y1_init.denote Ctxt.Valuation.nil).head
    == .value (BitVec.ofNat 512 2238717979393319499072711177537749483630111331377255661959129112147106072465884520903072835776448872258869191)

end Firedancer.Avx512

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg

/-!
# `@fd_f25519_d`

The initialiser of the module global, verbatim from
`build/native/gcc/mlir/ref/region/fd_f25519_d.mlir`. `ref.mlir` declares it
`constant, internal, alignment = 16, unnamed_addr = 0` -- the address is
significant, so no constant merging.

The lifted region is not referenced by any lifted *program*: `llvm.mlir.addressof`
reads the address out of `GlobalState.globals`, and this is what says what lives
there -- it is the loader's input and the spec's constant.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fd_f25519_d_region : MLIR.AST.Region 0 := [mlir_region|
{
    %0 = "llvm.mlir.constant"() <{value = dense<[929955233495203, 466365720129213, 1662059464998953, 2033849074728123, 1442794654840575]> : tensor<5xi64>}> : () -> !llvm.array<5 x i64>
    %1 = "llvm.mlir.undef"() : () -> !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>
    %2 = "llvm.insertvalue"(%1, %0) <{position = array<i64: 0>}> : (!llvm.struct<"struct.fd_f25519", (array<5 x i64>)>, !llvm.array<5 x i64>) -> !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>
    %3 = "llvm.mlir.undef"() : () -> !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>
    %4 = "llvm.insertvalue"(%3, %2) <{position = array<i64: 0>}> : (!llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>) -> !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>
    "llvm.return"(%4) : (!llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>) -> ()
}
]

/-- The global's contents, read off the artifact rather than retyped. -/
def fd_f25519_d_init : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 320] :=
  [sllvm_of| fd_f25519_d_region]

-- The five limbs, as `ref.mlir` writes them, packed little-endian by lane --
-- the layout `LLVM.Ty.flattenBV` gives an aggregate. Pins the lift against the
-- artifact, so a spec may quote the limbs without retyping them.
#guard InstCombine.LLVM.Ty.ofBitvec (fd_f25519_d_init.denote Ctxt.Valuation.nil).head
    == .value (BitVec.ofNat 320 167064207424422679488171221284707733579721947130980105998532069541309104583583025869939636387)
-- limbs: 929955233495203, 466365720129213, 1662059464998953, 2033849074728123, 1442794654840575

end Firedancer.Ref

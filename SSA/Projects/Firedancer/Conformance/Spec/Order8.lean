/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Spec.F25519
import SSA.Projects.Firedancer.Avx512.Spec.Common
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_order8_point_y0
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_order8_point_y1
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_order8_point_y0
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_order8_point_y1

/-!
# `@fd_ed25519_order8_point_y0` / `_y1`, both encodings

`fd_ed25519_affine_is_small_order` reaches these two globals through
`llvm.mlir.addressof`, so their addresses never enter a statement -- but what
they *hold* does, and the two backends hold different bytes for the same field
element: five 51-bit limbs on the ref side, six 43-bit limbs on the AVX-512
side.

The limbs below are pinned against the lifted initialisers by the `#guard`s at
the end of this file -- each is the artifact's own limbs packed little-endian by
64-bit lane, the layout `LLVM.Ty.flattenBV` gives an aggregate -- so a mistyped
digit fails to elaborate rather than silently changing the constant. They are
read off:
`build/native/gcc/mlir/{ref,avx512}/region/fd_ed25519_order8_point_y{0,1}.mlir`,
which is also where the region inlines them as the dead constants `%1` and `%7`.

The agreement lemmas are cheaper than they look. Both encodings are *already
reduced* -- each denotes a natural below `p` -- and the two naturals are equal
outright, so no modular step is involved: the identity is `Nat` arithmetic and
the cast to `ZMod p` rides along. `y1 = -y0`, but nothing here needs that.
-/

namespace Firedancer
open Ed25519

/-- `@fd_ed25519_order8_point_y0`, ref encoding: five 51-bit limbs. -/
def order8_y0_ref : Fin 5 → ℕ
  | 0 => 2166873539340326
  | 1 => 1778179147085316
  | 2 => 1886209374839743
  | 3 => 1223329526802818
  | 4 => 105300633354275

/-- `@fd_ed25519_order8_point_y0`, AVX-512 encoding: six 43-bit limbs. -/
def order8_y0_avx : Fin 6 → ℕ
  | 0 => 3034655877158
  | 1 => 7251661554934
  | 2 => 8531478563367
  | 3 => 3751701540842
  | 4 => 152657171260
  | 5 => 51416324880

/-- `@fd_ed25519_order8_point_y1`, ref encoding. -/
def order8_y1_ref : Fin 5 → ℕ
  | 0 => 84926274344903
  | 1 => 473620666599931
  | 2 => 365590438845504
  | 3 => 1028470286882429
  | 4 => 2146499180330972

/-- `@fd_ed25519_order8_point_y1`, AVX-512 encoding. -/
def order8_y1_avx : Fin 6 → ℕ
  | 0 => 5761437145031
  | 1 => 1544431467273
  | 2 => 264614458840
  | 3 => 5044391481365
  | 4 => 8643435850947
  | 5 => 1048095302895

/-- The two encodings of `y0` denote the same natural -- before any reduction. -/
theorem order8_y0_nat :
    order8_y0_ref 0 + 2 ^ 51 * order8_y0_ref 1 + 2 ^ 102 * order8_y0_ref 2
      + 2 ^ 153 * order8_y0_ref 3 + 2 ^ 204 * order8_y0_ref 4
      = Avx512.decodeNat order8_y0_avx := by
  simp only [order8_y0_ref, order8_y0_avx, Avx512.decodeNat_eq]
  norm_num

/-- ... and likewise for `y1`. -/
theorem order8_y1_nat :
    order8_y1_ref 0 + 2 ^ 51 * order8_y1_ref 1 + 2 ^ 102 * order8_y1_ref 2
      + 2 ^ 153 * order8_y1_ref 3 + 2 ^ 204 * order8_y1_ref 4
      = Avx512.decodeNat order8_y1_avx := by
  simp only [order8_y1_ref, order8_y1_avx, Avx512.decodeNat_eq]
  norm_num

/-! ### Pinning the limbs against the lifted initialisers

Each `#guard` packs the limb function above little-endian by 64-bit lane and
compares it against the global's own initialiser region. The AVX-512 pair is
liftable only because `llvm.insertvalue` now carries the field's `LLVM.Ty`
(LIMITATIONS 7.3); its field is a `vector<8xi64>`. -/

#guard InstCombine.LLVM.Ty.ofBitvec
    (Ref.fd_ed25519_order8_point_y0_init.denote Ctxt.Valuation.nil).head
  == .value (BitVec.ofNat 320
      12192980334104125021482886871177693777525971344877968693128941921943918399272126260480174118)

#guard InstCombine.LLVM.Ty.ofBitvec
    (Ref.fd_ed25519_order8_point_y1_init.denote Ctxt.Valuation.nil).head
  == .value (BitVec.ofNat 320
      248547624636709978242923700447254355626407866746149546498081162889696353806486883190232979399)

#guard InstCombine.LLVM.Ty.ofBitvec
    (Avx512.fd_ed25519_order8_point_y0_init.denote Ctxt.Valuation.nil).head
  == .value (BitVec.ofNat 512
      109824603378377742799366497336319773139601164200045246967266531110976483098768435934712383608117256877631526)

#guard InstCombine.LLVM.Ty.ofBitvec
    (Avx512.fd_ed25519_order8_point_y1_init.denote Ctxt.Valuation.nil).head
  == .value (BitVec.ofNat 512
      2238717979393319499072711177537749483630111331377255661959129112147106072465884520903072835776448872258869191)

end Firedancer

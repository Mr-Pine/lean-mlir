/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_unpack
public import SSA.Projects.Firedancer.Avx512.Spec.Quad

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- The `uint256` a `wv_t` holds. -/
def wvNat (u : Vector (BitVec 64) 4) : ℕ :=
  u[0].toNat + 2 ^ 64 * u[1].toNat + 2 ^ 128 * u[2].toNat + 2 ^ 192 * u[3].toNat

/-- A `uint256` is 256 bits wide. -/
theorem wvNat_lt (u : Vector (BitVec 64) 4) : wvNat u < 2 ^ 256 := by
  have h0 := u[0].isLt; have h1 := u[1].isLt
  have h2 := u[2].isLt; have h3 := u[3].isLt
  simp only [wvNat]
  omega

abbrev fd_r43x6_unpack_spec (u : Vector (BitVec 64) 4) : Prop :=
  let out := (fd_r43x6_unpack.denote
    (Ctxt.Valuation.singleton (u.map PoisonOr.value))).head

  ∃ v : Vector (BitVec 64) 8,
    out = v.map PoisonOr.value
    ∧ R43x6.Unpacked v
    ∧ R43x6.decode' v = (wvNat u : ℤ)
    ∧ v[6] = 0 ∧ v[7] = 0
    ∧ (wvNat u < 2 * p → R43x6.NearlyReduced v)
    ∧ (wvNat u < p → R43x6.Reduced v)

end Firedancer.Avx512

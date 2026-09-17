/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_double_scalar_mul_base
public import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_neg
public import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_frombytes_2x
public import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_double_scalar_mul_base
public import SSA.Projects.Firedancer.Common.Spec.Scalar.fd_curve25519_scalar_wnaf
public import SSA.Projects.Firedancer.Proof.Globals

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `fd_ed25519_base_point_wnaf_table` is at `g`, apart from `r`, and holds `Bt`: entry `k < 128`,
at byte `192k`, a `u44` QUAD whose `2d·T` is within `2p`'s limbs and whose slots are `Bt k`. -/
def BaseTableHolds (s : GlobalState) (r : Pointer) (Bt : ℕ → Ed25519.PrecomputedPoint) : Prop :=
  ∃ g, GlobalPtr s "fd_ed25519_base_point_wnaf_table" g ∧ g.id ≠ r.id ∧ ∀ k < 128,
    ∃ h : IsQuadPtr s.mem (g.withOffset (BitVec.ofNat 64 (192 * k))),
      (R43x6.U44 (readQuad h).v03 ∧ R43x6.U44 (readQuad h).v14 ∧ R43x6.U44 (readQuad h).v25)
      ∧ (readQuad h).NegBounds 3 ∧ Ed25519.PrecomputedPoint.ofSlots (readQuad h).toPoint = Bt k

/-- With `a` a well-formed `u44` point and the base-point table holding `(2k+1)·B`: returns `r`,
writes one QUAD into `r` and nothing else, and that QUAD is `u44` and represents
`(n₁ mod 2²⁵⁵)·a + (n₂ mod 2²⁵⁵)·B`. -/
abbrev fd_ed25519_double_scalar_mul_base_spec (r n1 a n2 : Pointer) (s : GlobalState) : Prop :=
  let invocation := runFunction (fd_ed25519_double_scalar_mul_base.denote
    (Ctxt.Valuation.ofHVector [.value n2, .value a, .value n1, .value r]ₕ))
  let result := StateT.run invocation s

  ∀ (_hr : IsQuadPtr s.mem r) (ha : IsQuadPtr s.mem a) (hn1 : IsByteBufPtr s.mem n1)
    (hn2 : IsByteBufPtr s.mem n2) (hA : (readQuad ha).toPoint.WellFormed),
  R43x6.U44 (readQuad ha).v03 → R43x6.U44 (readQuad ha).v14 → R43x6.U44 (readQuad ha).v25 →
  ∀ (Bt : ℕ → Ed25519.PrecomputedPoint), BaseTableHolds s r Bt →
  BaseVals Bt Ed25519.basePoint Ed25519.wellFormed_basePoint →
  ∃ s' : GlobalState, result = .value ([.value r]ₕ, s') ∧
  ∃ q : Quad,
    let output_state : GlobalState := { s with mem := s.mem.writeQuad r q }

    output_state ≈ s'
    ∧ q.toPoint.Represents (((readBuf hn1).toNat % 2 ^ 255) • (readQuad ha).toPoint.toAffine hA
      + ((readBuf hn2).toNat % 2 ^ 255) • Ed25519.basePoint.toAffine Ed25519.wellFormed_basePoint)
    ∧ R43x6.U44 q.v03 ∧ R43x6.U44 q.v14 ∧ R43x6.U44 q.v25

end Firedancer.Avx512

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.SLLVM.Dialect
public import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_double_scalar_mul_base
public import SSA.Projects.Firedancer.Ref.Spec.Point
public import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_double_scalar_mul_base
public import SSA.Projects.Firedancer.Proof.Globals

@[expose] public section

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `fd_ed25519_base_point_wnaf_table` holds `Bt`: entry `k < 128`, at byte `160k`, a point with
loose limbs whose slots are `Bt k`. -/
def BaseTableHolds (s : GlobalState) (Bt : ℕ → Ed25519.PrecomputedPoint) : Prop :=
  ∀ q,
    GlobalPtr s "fd_ed25519_base_point_wnaf_table" q →
      ∀ k < 128,
        ∃ h : IsPointPtr s.mem (q.withOffset (BitVec.ofNat 64 (160 * k))),
          (∀ i, LimbBounds.Loose (isCoordPtr h i)) ∧
            Ed25519.PrecomputedPoint.ofSlots (readPoint h) = Bt k

/-- With `a` a well-formed point at `Z = 1` and the base-point table holding `(2k+1)·B`: returns
`r`, writes nothing but `r`, stored `X, Y, Z, T` (byte offsets 0, 40, 120, 80), and `r` then
represents `(n₁ mod 2²⁵⁵)·a + (n₂ mod 2²⁵⁵)·B`, its limbs tight. -/
abbrev fd_ed25519_double_scalar_mul_base_spec (r n1 a n2 : Pointer) (s : GlobalState) : Prop :=
  let invocation :=
    runFunction
      (fd_ed25519_double_scalar_mul_base.denote
        (Ctxt.Valuation.ofHVector [.value n2, .value a, .value n1, .value r]ₕ))
  let result := StateT.run invocation s
  ∀ (hr : IsPointPtr s.mem r) (ha : IsPointPtr s.mem a) (hn1 : IsByteBufPtr s.mem n1)
    (hn2 : IsByteBufPtr s.mem n2) (hA : (readPoint ha).WellFormed),
    (readPoint ha).Z = 1 →
      ∀ (Bt : ℕ → Ed25519.PrecomputedPoint),
        BaseTableHolds s Bt →
          BaseVals Bt Ed25519.basePoint Ed25519.wellFormed_basePoint →
            ∃ s' : GlobalState,
              result = .value ([.value r]ₕ, s') ∧
                ∃ oX oY oZ oT : BitVec (5 * 64),
                  let outMem :=
                    (((s.mem.splice r oX).splice (r.withOffset 40) oY).splice (r.withOffset 120)
                          oZ).splice
                      (r.withOffset 80) oT
                  let output_state : GlobalState := { s with mem := outMem }
                  have hpt : IsPointPtr outMem r :=
                    isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hr)))
                  output_state ≈ s' ∧
                    (readPoint hpt).Represents
                      (((readBuf hn1).toNat % 2 ^ 255) • (readPoint ha).toAffine hA +
                        ((readBuf hn2).toNat % 2 ^ 255) •
                          Ed25519.basePoint.toAffine Ed25519.wellFormed_basePoint) ∧
                    AllLimbBounds hpt

end Firedancer.Ref

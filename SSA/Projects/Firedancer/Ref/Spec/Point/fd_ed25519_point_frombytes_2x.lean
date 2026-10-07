/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_frombytes_2x
public import SSA.Projects.Firedancer.Ref.Spec.Point.fd_ed25519_point_frombytes

@[expose] public section

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- Two decompressions, short-circuiting: `0` if both encodings name a point,
`-1` if the first does not, `-2` if the second does not.

The second call runs on the memory the first left, so the second buffer is
read -- and its squareness decided -- there: nothing here says `buf₂` misses
`r₁`, and the region does not need it to. On `-1` nothing is written at all,
on `-2` only `r₁`. -/
abbrev fd_ed25519_point_frombytes_2x_spec (r₁ buf₁ r₂ buf₂ : Pointer) (s : GlobalState)
    (hr₁ : IsPointPtr s.mem r₁) (hbuf₁ : IsByteBufPtr s.mem buf₁) (hr₂ : IsPointPtr s.mem r₂)
    (hbuf₂ : IsByteBufPtr s.mem buf₂) : Prop :=
  let invocation :=
    runFunction
      (fd_ed25519_point_frombytes_2x.denote
        (Ctxt.Valuation.ofHVector [.value buf₂, .value r₂, .value buf₁, .value r₁]ₕ))
  let result := StateT.run invocation s
  let sq₁ :=
    IsSquare ((decodeBytes (readBuf hbuf₁) ^ 2 - 1) / (d * decodeBytes (readBuf hbuf₁) ^ 2 + 1))
  ∃ (s' : GlobalState) (ret : LLVM.IntW 32),
    result = .value ([ret]ₕ, s') ∧
      (¬sq₁ → ret = .value (-1 : BitVec 32) ∧ s ≈ s') ∧
        (sq₁ →
          ∃ oX oY oZ oT : Fin 5 → BitVec 64,
            let m₁ := pointOutMem s.mem r₁ oX oY oZ oT
            have hr₂' : IsPointPtr m₁ r₂ :=
              isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hr₂)))
            have hbuf₂' : IsByteBufPtr m₁ buf₂ :=
              isByteBufPtr_splice
                (isByteBufPtr_splice (isByteBufPtr_splice (isByteBufPtr_splice hbuf₂)))
            let sq₂ :=
              IsSquare
                ((decodeBytes (readBuf hbuf₂') ^ 2 - 1) /
                  (d * decodeBytes (readBuf hbuf₂') ^ 2 + 1))
            DecodesTo s.mem r₁ buf₁ hr₁ hbuf₁ oX oY oZ oT ∧
              DecodedBounds s.mem r₁ hr₁ oX oY oZ oT ∧
              (¬sq₂ → ret = .value (-2 : BitVec 32) ∧ s' ≈ ({ s with mem := m₁ } : GlobalState)) ∧
              (sq₂ →
                ∃ pX pY pZ pT : Fin 5 → BitVec 64,
                  ret = .value (0 : BitVec 32) ∧
                    s' ≈ ({ s with mem := pointOutMem m₁ r₂ pX pY pZ pT } : GlobalState) ∧
                    DecodesTo m₁ r₂ buf₂ hr₂' hbuf₂' pX pY pZ pT ∧
                    DecodedBounds m₁ r₂ hr₂' pX pY pZ pT))

end Firedancer.Ref

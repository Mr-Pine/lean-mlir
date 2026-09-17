/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_neg
public import SSA.Projects.Firedancer.Avx512.Spec.Quad
public import SSA.Projects.Firedancer.Curve

/-!
# `fd_ed25519_point_neg` (AVX-512)

`r = -a` as the projective coordinates `(-X : Y : Z : -T)`, as on the ref side.

The region computes `2p - a` on the `X` and `T` lanes with a plain, wrapping
`sub`, so the value is right only if no limb of `a.X` or `a.T` exceeds `2p`'s:
`NegBounds`. The fold that follows leaves *every* element within those bounds,
whatever it was given, so the result can be negated again.

`r.id ≠ a.id` because the region reloads `a`'s `14` and `25` vectors after
storing to `r`. The in-place `fd_ed25519_point_neg( A, A )` is not covered.
-/

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- `2p` limbwise, as the region subtracts from it: `2^44 - 38`, then
`2^44 - 2` four times, then `2^41 - 2`. -/
def twoPLimb : Fin 6 → ℕ :=
  ![17592186044378, 17592186044414, 17592186044414, 17592186044414, 17592186044414,
    2199023255550]

/-- Element `j` of `q` is at most `2p` limb for limb: `2p - q_j` does not wrap. -/
abbrev Quad.NegBounds (q : Quad) (j : Fin 4) : Prop :=
  ∀ k, q.vectorFunc j k ≤ twoPLimb k

abbrev fd_ed25519_point_neg_spec (r a : Pointer) (s : GlobalState)
    (_ : r.id ≠ a.id)
    (_hr : IsQuadPtr s.mem r) (ha : IsQuadPtr s.mem a) : Prop :=
  let invocation := runFunction
    (fd_ed25519_point_neg.denote (Ctxt.Valuation.ofHVector [.value a, .value r]ₕ))
  let result := StateT.run invocation s
  let q := readQuad ha
  let P := q.toPoint

  q.NegBounds 0 → q.NegBounds 3 →
  ∃ s' : GlobalState, result = .value ([.value r]ₕ, s') ∧
  ∃ q' : Quad,
    let output_state : GlobalState := { s with mem := s.mem.splice r q'.BV }
    output_state ≈ s'
    ∧ q'.toPoint = { X := -P.X, Y := P.Y, Z := P.Z, T := -P.T }
    ∧ ∀ j, q'.NegBounds j

end Firedancer.Avx512

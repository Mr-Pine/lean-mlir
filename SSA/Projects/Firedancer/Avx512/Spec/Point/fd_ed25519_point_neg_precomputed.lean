/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_neg_precomputed
public import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_neg
public import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_frombytes_2x
public import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_point_sub_with_opts

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- `r = -a` for a precomputed `a`: `(Y + X, Y - X, Z, 2p - 2d·T)` from
`(Y - X, Y + X, Z, 2d·T)`. The `T` lanes are subtracted from `2p` with no fold,
so `a`'s must not exceed `2p`'s limbs; the rest are copied. The region stores `r`
twice, the second covering the first; `r` and `a` lie in different blocks. -/
abbrev fd_ed25519_point_neg_precomputed_spec (r a : Pointer) (s : GlobalState)
    (_ : r.id ≠ a.id) (_hr : IsQuadPtr s.mem r) (ha : IsQuadPtr s.mem a) : Prop :=
  let invocation := runFunction
    (fd_ed25519_point_neg_precomputed.denote (Ctxt.Valuation.ofHVector [.value a, .value r]ₕ))
  let result := StateT.run invocation s
  let q := readQuad ha

  R43x6.U44 q.v03 → R43x6.U44 q.v14 → R43x6.U44 q.v25 → q.NegBounds 3 →
  ∃ s' : GlobalState, result = .value ([.value r]ₕ, s') ∧
  ∃ q' : Quad,
    let output_state : GlobalState := { s with mem := s.mem.writeQuad r q' }
    output_state ≈ s'
    ∧ PrecomputedPoint.ofSlots q'.toPoint = (PrecomputedPoint.ofSlots q.toPoint).neg
    ∧ R43x6.U44 q'.v03 ∧ R43x6.U44 q'.v14 ∧ R43x6.U44 q'.v25

end Firedancer.Avx512

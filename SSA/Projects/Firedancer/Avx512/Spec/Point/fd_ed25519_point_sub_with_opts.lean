/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_sub_with_opts
public import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_neg
public import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_frombytes_2x
public import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_point_sub_with_opts

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- `r = a.addPrecomputed b.neg` for `b_is_precomputed = 1`:
`fd_ed25519_point_neg_precomputed` into a local, then
`fd_ed25519_point_add_with_opts`, `u44` in and out. As in add, gcc drops
`b_Z_is_one` and `skip_last_mul`. The negation subtracts `b`'s `T` lanes from `2p`
unfolded, so they must not exceed `2p`'s limbs. `r` is stored only after `a` and
the local are loaded, so it may overlap `a` or `b`. -/
abbrev fd_ed25519_point_sub_with_opts_spec (r a b : Pointer) (bPre : BitVec 32)
    (s : GlobalState) (_hr : IsQuadPtr s.mem r) (ha : IsQuadPtr s.mem a)
    (hb : IsQuadPtr s.mem b) : Prop :=
  let invocation := runFunction (fd_ed25519_point_sub_with_opts.denote
    (Ctxt.Valuation.ofHVector [.value bPre, .value b, .value a, .value r]ₕ))
  let result := StateT.run invocation s
  let qa := readQuad ha
  let qb := readQuad hb

  bPre = 1 →
  R43x6.U44 qa.v03 → R43x6.U44 qa.v14 → R43x6.U44 qa.v25 →
  R43x6.U44 qb.v03 → R43x6.U44 qb.v14 → R43x6.U44 qb.v25 → qb.NegBounds 3 →
  ∃ s' : GlobalState, result = .value ([.value r]ₕ, s') ∧
  ∃ q' : Quad,
    let output_state : GlobalState := { s with mem := s.mem.writeQuad r q' }
    output_state ≈ s'
    ∧ q'.toPoint = qa.toPoint.addPrecomputed (PrecomputedPoint.ofSlots qb.toPoint).neg
    ∧ R43x6.U44 q'.v03 ∧ R43x6.U44 q'.v14 ∧ R43x6.U44 q'.v25

end Firedancer.Avx512

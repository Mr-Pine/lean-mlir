/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_add_with_opts
public import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_frombytes_2x
public import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_point_add_with_opts

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- `r = a.addPrecomputed b` for `b_is_precomputed = 1`, `FD_R43X6_GE_ADD_TABLE_ALT`,
`u44` in and out. gcc drops the unused `b_Z_is_one` and `skip_last_mul`
parameters: the sum is always multiplied out and `b`'s `Z` always read. `a` and
`b` are loaded before any store, so either may overlap `r`. -/
abbrev fd_ed25519_point_add_with_opts_spec (r a b : Pointer) (bPre : BitVec 32)
    (s : GlobalState) (_hr : IsQuadPtr s.mem r) (ha : IsQuadPtr s.mem a)
    (hb : IsQuadPtr s.mem b) : Prop :=
  let invocation := runFunction (fd_ed25519_point_add_with_opts.denote
    (Ctxt.Valuation.ofHVector [.value bPre, .value b, .value a, .value r]ₕ))
  let result := StateT.run invocation s
  let qa := readQuad ha
  let qb := readQuad hb

  bPre = 1 →
  R43x6.U44 qa.v03 → R43x6.U44 qa.v14 → R43x6.U44 qa.v25 →
  R43x6.U44 qb.v03 → R43x6.U44 qb.v14 → R43x6.U44 qb.v25 →
  ∃ s' : GlobalState, result = .value ([.value r]ₕ, s') ∧
  ∃ q' : Quad,
    let output_state : GlobalState := { s with mem := s.mem.writeQuad r q' }

    output_state ≈ s'
    ∧ q'.toPoint = qa.toPoint.addPrecomputed (PrecomputedPoint.ofSlots qb.toPoint)
    ∧ R43x6.U44 q'.v03 ∧ R43x6.U44 q'.v14 ∧ R43x6.U44 q'.v25

end Firedancer.Avx512

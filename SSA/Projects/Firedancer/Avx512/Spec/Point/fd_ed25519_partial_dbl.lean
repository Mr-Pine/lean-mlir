/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_partial_dbl
public import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_frombytes_2x
public import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_point_dbln

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- `r = a.dbl`, `FD_R43X6_GE_DBL`, `u44` in and out. Unlike ref's `partialDbl`
this is the whole doubling; AVX-512 `fd_ed25519_point_add_final_mul` only copies.
`a` is loaded before any store, so it may overlap `r`. -/
abbrev fd_ed25519_partial_dbl_spec (r a : Pointer) (s : GlobalState)
    (_hr : IsQuadPtr s.mem r) (ha : IsQuadPtr s.mem a) : Prop :=
  let invocation := runFunction
    (fd_ed25519_partial_dbl.denote (Ctxt.Valuation.ofHVector [.value a, .value r]ₕ))
  let result := StateT.run invocation s
  let q := readQuad ha

  R43x6.U44 q.v03 → R43x6.U44 q.v14 → R43x6.U44 q.v25 →
  ∃ s' : GlobalState, result = .value ([.value r]ₕ, s') ∧
  ∃ q' : Quad,
    let output_state : GlobalState := { s with mem := s.mem.writeQuad r q' }

    output_state ≈ s'
    ∧ q'.toPoint = q.toPoint.dbl
    ∧ R43x6.U44 q'.v03 ∧ R43x6.U44 q'.v14 ∧ R43x6.U44 q'.v25

end Firedancer.Avx512

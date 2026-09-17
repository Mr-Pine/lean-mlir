/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_add_final_mul_projective
public import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_frombytes_2x

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- `r = a` via `fd_ed25519_point_set`, as in `fd_ed25519_point_add_final_mul`:
AVX-512 point add leaves nothing to multiply. Unlike ref, `T` is copied too.
`r` and `a` lie in different blocks. -/
abbrev fd_ed25519_point_add_final_mul_projective_spec (r a : Pointer) (s : GlobalState)
    (_ : r.id ≠ a.id) (_hr : IsQuadPtr s.mem r) (ha : IsQuadPtr s.mem a) : Prop :=
  let invocation := runFunction
    (fd_ed25519_point_add_final_mul_projective.denote
      (Ctxt.Valuation.ofHVector [.value a, .value r]ₕ))
  let result := StateT.run invocation s
  let output_state : GlobalState := { s with mem := s.mem.writeQuad r (readQuad ha) }

  ∃ s' : GlobalState, result = .value ([.value r]ₕ, s') ∧ output_state ≈ s'

end Firedancer.Avx512

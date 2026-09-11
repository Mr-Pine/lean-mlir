/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_add_final_mul
import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_frombytes_2x

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- `r = a` via `fd_ed25519_point_set`: AVX-512 point add ignores
`skip_last_mul`, so no multiplication is left. The C declares `r` `restrict`;
here `r` and `a` lie in different blocks. -/
abbrev fd_ed25519_point_add_final_mul_spec (r a : Pointer) (s : GlobalState)
    (_ : r.id ≠ a.id) (_hr : IsQuadPtr s.mem r) (ha : IsQuadPtr s.mem a) : Prop :=
  let invocation := runFunction
    (fd_ed25519_point_add_final_mul.denote (Ctxt.Valuation.ofHVector [.value a, .value r]ₕ))
  let result := StateT.run invocation s
  let output_state : GlobalState := { s with mem := s.mem.writeQuad r (readQuad ha) }

  ∃ s' : GlobalState, result = .value ([.value r]ₕ, s') ∧ output_state ≈ s'

end Firedancer.Avx512

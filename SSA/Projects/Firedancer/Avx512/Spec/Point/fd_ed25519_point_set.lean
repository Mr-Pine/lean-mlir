/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_set
import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_frombytes_2x

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- `r = a`: the QUAD `a` holds, stored whole into `r`. Each vector's store
follows its load, so `r` and `a` lie in different blocks. -/
abbrev fd_ed25519_point_set_spec (r a : Pointer) (s : GlobalState)
    (_ : r.id ≠ a.id) (_hr : IsQuadPtr s.mem r) (ha : IsQuadPtr s.mem a) : Prop :=
  let invocation := runFunction
    (fd_ed25519_point_set.denote (Ctxt.Valuation.ofHVector [.value a, .value r]ₕ))
  let result := StateT.run invocation s
  let output_state : GlobalState := { s with mem := s.mem.writeQuad r (readQuad ha) }

  ∃ s' : GlobalState, result = .value ([.value r]ₕ, s') ∧ output_state ≈ s'

end Firedancer.Avx512

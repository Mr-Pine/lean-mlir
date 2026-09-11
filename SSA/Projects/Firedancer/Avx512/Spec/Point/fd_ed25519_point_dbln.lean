/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_dbln
import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_frombytes_2x
import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_point_dbln

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- `r = 2^n a`, `FD_R43X6_GE_DBL` repeated, `u44` in and out. `^bb0` stores the
first doubling into `r` and the loop's exit stores the last over it, so the
memory is one QUAD store. `a` is loaded before any store, so it may overlap
`r`. -/
abbrev fd_ed25519_point_dbln_spec (r a : Pointer) (n : BitVec 32) (s : GlobalState)
    (_hr : IsQuadPtr s.mem r) (ha : IsQuadPtr s.mem a) : Prop :=
  let invocation := runFunction
    (fd_ed25519_point_dbln.denote (Ctxt.Valuation.ofHVector [.value n, .value a, .value r]ₕ))
  let result := StateT.run invocation s
  let q := readQuad ha

  ∃ q' : Quad,
    let output_state : GlobalState := { s with mem := s.mem.writeQuad r q' }

    (∃ s' : GlobalState, result = .value ([.value r]ₕ, s') ∧ output_state ≈ s')
    ∧ q'.toPoint = q.toPoint.dbln n
    ∧ R43x6.U44 q'.v03 ∧ R43x6.U44 q'.v14 ∧ R43x6.U44 q'.v25

end Firedancer.Avx512

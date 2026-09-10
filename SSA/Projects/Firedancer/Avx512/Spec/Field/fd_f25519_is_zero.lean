/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_f25519_is_zero
import SSA.Projects.Firedancer.Avx512.Spec.Vec
import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_r43x6_ge_is_eq

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

abbrev fd_f25519_is_zero_spec (q : Pointer) (s : GlobalState)
    (hq : IsVecPtr s.mem q) : Prop :=
  let invocation := runFunction (fd_f25519_is_zero.denote (Ctxt.Valuation.singleton (.value q)))
  let result := StateT.run invocation s
  let v := readVec hq
  let isZero := vecValue v = 0
  let output : LLVM.IntW _ := .value (if isZero then 1#32 else 0#32)

  R43x6.NearlyReduced v → v[6] = 0 → v[7] = 0 →
    ∃ s' : GlobalState, result = .value ([output]ₕ, s') ∧ s ≈ s'

end Firedancer.Avx512

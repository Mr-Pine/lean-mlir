/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_f25519_eq
import SSA.Projects.Firedancer.Avx512.Spec.Vec
import SSA.Projects.Firedancer.Curve

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

abbrev fd_f25519_eq_spec (p q : Pointer) (s : GlobalState)
    (hp : IsVecPtr s.mem p) (hq : IsVecPtr s.mem q) : Prop :=
  let invocation := runFunction (fd_f25519_eq.denote (Ctxt.Valuation.ofPair (.value q) (.value p)))
  let result := StateT.run invocation s
  let output_value : LLVM.IntW _ :=
    .value (if vecValue (readVec hp) = vecValue (readVec hq) then 1#32 else 0#32)

  R43x6.Reduced (readVec hp) → R43x6.Reduced (readVec hq) →
    ∃ s' : GlobalState, result = .value ([output_value]ₕ, s') ∧ s ≈ s'

end Firedancer.Avx512

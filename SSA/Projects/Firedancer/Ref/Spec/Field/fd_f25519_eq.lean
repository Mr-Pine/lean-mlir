import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_eq
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

abbrev fd_f25519_eq_spec (p q: Pointer) (s: GlobalState)
    (hp : IsFieldElemPtr s.mem p) (hq : IsFieldElemPtr s.mem q) : Prop :=
  let invocation := runFunction (fd_f25519_eq.denote (Ctxt.Valuation.ofPair (.value q) (.value p)))
  let result := StateT.run invocation s
  let output_value: LLVM.IntW _ :=
    .value (if readFieldElem hp = readFieldElem hq then 1#32 else 0#32)

  ∃ s' : GlobalState , result = .value ([output_value]ₕ, s') ∧ s ≈ s'

end Firedancer.Ref

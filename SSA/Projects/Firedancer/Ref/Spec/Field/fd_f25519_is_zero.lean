import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_is_zero
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

abbrev fd_f25519_is_zero_spec (p: Pointer) (s: GlobalState) : Prop :=
  let invocation := runFunction (fd_f25519_is_zero.denote (Ctxt.Valuation.singleton (.value p)))
  let result := StateT.run invocation s
  let extracted_value := readFieldElem? p s.mem
  let is_zero := extracted_value = .some 0
  let output_value: LLVM.IntW _ := .value (if is_zero then 1#32 else 0#32)

  ∃ s' : GlobalState , result = .value ([output_value]ₕ, s') ∧ s ≈ s'



end Firedancer.Ref

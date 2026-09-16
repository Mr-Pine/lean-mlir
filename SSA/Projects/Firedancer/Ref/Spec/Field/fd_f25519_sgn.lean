import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_sgn
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- The sign of a field element: the low bit of its canonical representative,
read off the serialised form's first byte. The state survives untouched -- the
32-byte buffer is a local. -/
abbrev fd_f25519_sgn_spec (q : Pointer) (s : GlobalState) (hq : IsFieldElemPtr s.mem q) : Prop :=
  let invocation := runFunction (fd_f25519_sgn.denote (Ctxt.Valuation.singleton (.value q)))
  let result := StateT.run invocation s
  let a := readFieldElem hq
  ∃ s' : GlobalState, result = .value ([.value (BitVec.ofNat 32 (a.val % 2))]ₕ, s') ∧ s ≈ s'

end Firedancer.Ref

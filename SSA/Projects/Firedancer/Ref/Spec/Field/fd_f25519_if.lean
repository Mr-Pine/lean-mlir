import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_if
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

abbrev fd_f25519_if_spec (r : Pointer) (cond : BitVec 32) (a0 a1 : Pointer) (s : GlobalState)
    (hr : IsFieldElemPtr s.mem r) (h0 : IsFieldElemPtr s.mem a0) (h1 : IsFieldElemPtr s.mem a1) :
    Prop :=
  let invocation :=
    runFunction
      (fd_f25519_if.denote
        (Ctxt.Valuation.ofHVector [.value a1, .value a0, .value cond, .value r]ₕ))
  let result := StateT.run invocation s
  let a0In := readFieldElem h0
  let a1In := readFieldElem h1
  -- `cond` reaches `selectznz` truncated, so only its low byte decides.
  let taken := cond.setWidth 8 ≠ 0
  let srcPtr := if taken then a0 else a1
  have hsrcPtr : IsFieldElemPtr s.mem srcPtr := by grind only
  let out := if taken then a0In else a1In
  let output_state : GlobalState :=
    { s with mem := s.mem.splice r (packLimbs (fun i => readLimb i hsrcPtr)) }
  readFieldElem (m := output_state.mem) (isFieldElemPtr_splice hr) = out ∧
    (∃ s' : GlobalState, result = .value ([.value r]ₕ, s') ∧ output_state ≈ s')

end Firedancer.Ref

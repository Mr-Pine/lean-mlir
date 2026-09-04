import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_mul
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

abbrev fd_f25519_mul_spec (o p q: Pointer) (s: GlobalState)
    (ho : IsFieldElemPtr s.mem o)
    (hp : IsFieldElemPtr s.mem p) (hq : IsFieldElemPtr s.mem q) : Prop :=
  let invocation := runFunction (fd_f25519_mul.denote (Ctxt.Valuation.ofHVector [.value q, .value p, .value o]ₕ))
  let result := StateT.run invocation s
  let p_input := readFieldElem hp
  let q_input := readFieldElem hq

  ∃ out : BitVec (5 * 64),
    let output_state : GlobalState := { s with mem := s.mem.splice o out }

    readFieldElem (m := output_state.mem) (isFieldElemPtr_splice ho) = p_input * q_input
    ∧ LimbBounds (m := output_state.mem) (isFieldElemPtr_splice ho)
    ∧ (∃ s' : GlobalState , result = .value ([.value o]ₕ, s') ∧ output_state ≈ s')

end Firedancer.Ref

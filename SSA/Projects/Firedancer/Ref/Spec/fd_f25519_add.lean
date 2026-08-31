import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.fd_f25519_add
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- Unlike `fiat_25519_add`, the wrapper carries afterwards, so the limbs come
back down to the tight bound. -/
abbrev fd_f25519_add_spec (o p q: Pointer) (s: GlobalState)
    (ho : IsFieldElemPtr s.mem o) (hp : IsFieldElemPtr s.mem p)
    (hq : IsFieldElemPtr s.mem q) : Prop :=
  let invocation := runFunction (fd_f25519_add.denote (Ctxt.Valuation.ofHVector [.value q, .value p, .value o]ₕ ))
  let result := StateT.run invocation s
  let p_input := readFieldElem p s.mem hp
  let q_input := readFieldElem q s.mem hq

  ∃ out : Fin 5 → BitVec 64,
    let output_state : GlobalState := { s with mem := s.mem.splice o (packLimbs out) }

    readFieldElem o output_state.mem (isFieldElemPtr_splice ho) = p_input + q_input
    ∧ LimbBounds (m := output_state.mem) (isFieldElemPtr_splice ho)
    ∧ (∃ s' : GlobalState , result = .value ([.value o]ₕ, s') ∧ output_state ≈ s')

end Firedancer.Ref

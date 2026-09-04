import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_sub
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

abbrev fiat_25519_sub_spec (o p q: Pointer) (s: GlobalState)
    (ho : IsFieldElemPtr s.mem o)
    (hp : IsFieldElemPtr s.mem p) (hq : IsFieldElemPtr s.mem q) : Prop :=
  let invocation := runFunction (fiat_25519_sub.denote (Ctxt.Valuation.ofHVector [.value q, .value p, .value o]ₕ ))
  let result := StateT.run invocation s
  let p_input := readFieldElem hp
  let q_input := readFieldElem hq

  ∃ out : BitVec (5 * 64),
    let output_state : GlobalState := { s with mem := s.mem.splice o out }

    readFieldElem (m := output_state.mem) (isFieldElemPtr_splice ho) = p_input - q_input
    -- no carry, so the limbs come back at the loose bound
    ∧ LimbBounds.Loose (m := output_state.mem) (isFieldElemPtr_splice ho)
    ∧ (∃ s' : GlobalState , result = .value ([]ₕ, s') ∧ output_state ≈ s')

end Firedancer.Ref

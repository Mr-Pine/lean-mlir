import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_add
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `fiat_25519_add` adds limbwise without carrying, so the result is a *loose*
field element: the value is the sum, but the limbs are only bounded by the loose
bound `fiat_25519_carry` accepts. -/
abbrev fiat_25519_add_spec (o p q: Pointer) (s: GlobalState)
    (ho : IsFieldElemPtr s.mem o) (hp : IsFieldElemPtr s.mem p)
    (hq : IsFieldElemPtr s.mem q) : Prop :=
  let invocation := runFunction (fiat_25519_add.denote (Ctxt.Valuation.ofHVector [.value q, .value p, .value o]ₕ ))
  let result := StateT.run invocation s
  let p_input := readFieldElem hp
  let q_input := readFieldElem hq

  ∃ out : Fin 5 → BitVec 64,
    let output_state : GlobalState := { s with mem := s.mem.splice o (packLimbs out) }

    readFieldElem (m := output_state.mem) (isFieldElemPtr_splice ho) = p_input + q_input
    ∧ LimbBounds (m := output_state.mem) (isFieldElemPtr_splice ho) 0x18000000000000
    ∧ (∃ s' : GlobalState , result = .value ([]ₕ, s') ∧ output_state ≈ s')

end Firedancer.Ref

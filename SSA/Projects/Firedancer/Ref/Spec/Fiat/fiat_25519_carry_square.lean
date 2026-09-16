import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_carry_square
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

abbrev fiat_25519_carry_square_spec (o p : Pointer) (s : GlobalState) (ho : IsFieldElemPtr s.mem o)
    (hp : IsFieldElemPtr s.mem p) : Prop :=
  let invocation :=
    runFunction (fiat_25519_carry_square.denote (Ctxt.Valuation.ofHVector [.value p, .value o]ₕ))
  let result := StateT.run invocation s
  let p_input := readFieldElem hp
  ∃ out : Fin 5 → BitVec 64,
    let output_state : GlobalState := { s with mem := s.mem.splice o (packLimbs out) }
    readFieldElem (m := output_state.mem) (isFieldElemPtr_splice ho) = p_input * p_input ∧
      LimbBounds (m := output_state.mem) (isFieldElemPtr_splice ho) ∧
      (∃ s' : GlobalState, result = .value ([]ₕ, s') ∧ output_state ≈ s')
      -- all-zero limbs come only from an all-zero operand
      ∧ (ZeroLimbs o output_state.mem → ZeroLimbs p s.mem)

end Firedancer.Ref

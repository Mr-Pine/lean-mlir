module

public import SSA.Projects.SLLVM.Dialect
public import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_carry_mul
public import SSA.Projects.Firedancer.Ref.Spec.F25519

@[expose] public section

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

abbrev fiat_25519_carry_mul_spec (o p q : Pointer) (s : GlobalState) (hp : IsFieldElemPtr s.mem p)
    (hq : IsFieldElemPtr s.mem q) : Prop :=
  let invocation :=
    runFunction
      (fiat_25519_carry_mul.denote (Ctxt.Valuation.ofHVector [.value q, .value p, .value o]ₕ))
  let result := StateT.run invocation s
  let p_input := readFieldElem hp
  let q_input := readFieldElem hq
  ∃ out : BitVec (5 * 64),
    let output_state : GlobalState := { s with mem := s.mem.splice o out }
    decodeFieldElem (fun i => (out.extractLsb' (64 * i.toNat) 64).toNat) = p_input * q_input ∧
      (∃ s' : GlobalState, result = .value ([]ₕ, s') ∧ output_state ≈ s') ∧
      (∀ (i : Fin 5) (l : ℕ), readLimb? o i output_state.mem = some l → l ≤ 0x8000000000000)
      -- all-zero limbs come only from an all-zero operand
      ∧ (ZeroLimbs o output_state.mem → ZeroLimbs p s.mem ∨ ZeroLimbs q s.mem)

end Firedancer.Ref

module

public import SSA.Projects.SLLVM.Dialect
public import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_pow22523
public import SSA.Projects.Firedancer.Ref.Spec.F25519

@[expose] public section

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `r = a^(2^252 - 3)`, the power the inverse-square-root chain needs; the
chain ends in `fd_f25519_mul`, so the limbs come back tight. -/
abbrev fd_f25519_pow22523_spec (o p : Pointer) (s : GlobalState) (ho : IsFieldElemPtr s.mem o)
    (hp : IsFieldElemPtr s.mem p) : Prop :=
  let invocation :=
    runFunction (fd_f25519_pow22523.denote (Ctxt.Valuation.ofHVector [.value p, .value o]ₕ))
  let result := StateT.run invocation s
  let p_input := readFieldElem hp
  ∃ out : Fin 5 → BitVec 64,
    let output_state : GlobalState := { s with mem := s.mem.splice o (packLimbs out) }
    readFieldElem (m := output_state.mem) (isFieldElemPtr_splice ho) = p_input ^ (2 ^ 252 - 3) ∧
      LimbBounds (m := output_state.mem) (isFieldElemPtr_splice ho) ∧
      (∃ s' : GlobalState, result = .value ([.value o]ₕ, s') ∧ output_state ≈ s')
      -- all-zero limbs come only from an all-zero input
      ∧ (ZeroLimbs o output_state.mem → ZeroLimbs p s.mem)

end Firedancer.Ref

module

public import SSA.Projects.SLLVM.Dialect
public import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_neg
public import SSA.Projects.Firedancer.Ref.Spec.Bias

@[expose] public section

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `r = -a`. Unlike `fd_f25519_add`/`sub` the wrapper does *not* carry, so the
limbs stay at `fiat_25519_opp`'s bias bound, not the tight one -- per limb,
which is what lets `fd_f25519_eq` take the result as its subtrahend. -/
abbrev fd_f25519_neg_spec (o q : Pointer) (s : GlobalState) (ho : IsFieldElemPtr s.mem o)
    (hq : IsFieldElemPtr s.mem q) : Prop :=
  let invocation :=
    runFunction (fd_f25519_neg.denote (Ctxt.Valuation.ofHVector [.value q, .value o]ₕ))
  let result := StateT.run invocation s
  let q_input := readFieldElem hq
  ∃ out : BitVec (5 * 64),
    let output_state : GlobalState := { s with mem := s.mem.splice o out }
    readFieldElem (m := output_state.mem) (isFieldElemPtr_splice ho) = -q_input ∧
      BiasBounds (m := output_state.mem) (isFieldElemPtr_splice ho) ∧
      (∃ s' : GlobalState, result = .value ([.value o]ₕ, s') ∧ output_state ≈ s')

end Firedancer.Ref

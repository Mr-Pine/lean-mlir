import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_neg
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `r = -a`. Unlike `fd_f25519_add`/`sub` the wrapper does *not* carry, so the
limbs stay at `fiat_25519_opp`'s bias bound, not the tight one. -/
abbrev fd_f25519_neg_spec (o q: Pointer) (s: GlobalState) : Prop :=
  let invocation := runFunction (fd_f25519_neg.denote (Ctxt.Valuation.ofHVector [.value q, .value o]ₕ))
  let result := StateT.run invocation s
  let q_input := readFieldElem? q s.mem

  ∃ out : BitVec (5 * 64),
    let output_state : GlobalState := { s with mem := s.mem.splice o out }

    (∃ s' : GlobalState , result = .value ([.value o]ₕ, s') ∧ output_state ≈ s')
    ∧ readFieldElem? o output_state.mem = Neg.neg <$> q_input
    ∧ ∀ (i : Fin 5) (l : ℕ), readLimb? o i output_state.mem = some l → l ≤ 0xffffffffffffe

end Firedancer.Ref

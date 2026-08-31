import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_opp
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- Limbwise `2·p - a`, i.e. `fiat_25519_sub` with the bias as minuend: no
carry, so the limbs come back bounded by the bias limbs themselves. -/
abbrev fiat_25519_opp_spec (o q: Pointer) (s: GlobalState) : Prop :=
  let invocation := runFunction (fiat_25519_opp.denote (Ctxt.Valuation.ofHVector [.value q, .value o]ₕ))
  let result := StateT.run invocation s
  let q_input := readFieldElem? q s.mem

  ∃ out : BitVec (5 * 64),
    let output_state : GlobalState := { s with mem := s.mem.splice o out }

    (∃ s' : GlobalState , result = .value ([]ₕ, s') ∧ output_state ≈ s')
    ∧ readFieldElem? o output_state.mem = Neg.neg <$> q_input
    ∧ ∀ (i : Fin 5) (l : ℕ), readLimb? o i output_state.mem = some l → l ≤ 0xffffffffffffe

end Firedancer.Ref

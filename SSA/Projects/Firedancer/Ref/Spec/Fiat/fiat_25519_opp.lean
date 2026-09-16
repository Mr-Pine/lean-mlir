import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_opp
import SSA.Projects.Firedancer.Ref.Spec.Bias

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- Limbwise `2·p - a`, i.e. `fiat_25519_sub` with the bias as minuend: no
carry, so the limbs come back bounded by the bias limbs themselves -- per
limb, which is what `fiat_25519_sub` needs to take the result as subtrahend. -/
abbrev fiat_25519_opp_spec (o q : Pointer) (s : GlobalState) (ho : IsFieldElemPtr s.mem o)
    (hq : IsFieldElemPtr s.mem q) : Prop :=
  let invocation :=
    runFunction (fiat_25519_opp.denote (Ctxt.Valuation.ofHVector [.value q, .value o]ₕ))
  let result := StateT.run invocation s
  let q_input := readFieldElem hq
  ∃ out : BitVec (5 * 64),
    let output_state : GlobalState := { s with mem := s.mem.splice o out }
    readFieldElem (m := output_state.mem) (isFieldElemPtr_splice ho) = -q_input ∧
      BiasBounds (m := output_state.mem) (isFieldElemPtr_splice ho) ∧
      (∃ s' : GlobalState, result = .value ([]ₕ, s') ∧ output_state ≈ s')
      -- limbwise `bias - q`
      ∧ (∀ i, readLimb? o i output_state.mem = some (biasLimb i - readLimb i hq))

end Firedancer.Ref

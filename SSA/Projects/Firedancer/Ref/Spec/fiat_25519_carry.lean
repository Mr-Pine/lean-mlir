import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.fiat_25519_carry
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `fiat_25519_carry` writes `p₁`'s field element back to `p₀`, carried: the
value is unchanged and every limb is at most `2^51`. The only lasting effect is
the 5*64 bits spliced at `p₀` -- allocation counter, other blocks, and the rest
of `p₀`'s block come along unchanged from the record update. -/
abbrev fiat_25519_carry_spec (p₀ p₁: Pointer) (s: GlobalState) : Prop :=
  let invocation := (fiat_25519_carry.denote (Ctxt.Valuation.ofPair (.value p₁) (.value p₀)))
  let result := StateT.run invocation s
  let input_value := readFieldElem? p₁ s.mem

  ∃ out : BitVec (5 * 64),
    let output_state : GlobalState := { s with mem := s.mem.splice p₀ out }

    (∃ s' : GlobalState , result = .value ([]ₕ, s') ∧ output_state ≈ s')
    ∧ readFieldElem? p₀ output_state.mem = input_value
    ∧ ∀ (i : Fin 5) (l : ℕ), readLimb? p₀ i output_state.mem = some l → l ≤ 0x8000000000000

end Firedancer.Ref

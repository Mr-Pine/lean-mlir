import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_to_bytes
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- Full reduction and serialisation: the 32-byte little-endian buffer at `o`
holds the canonical representative of the field element at `q`. Correct for a
carried element (limbs `≤ 2^51`, so the value is below `2·p` and one
conditional subtraction canonicalises it); the bound is the conformance
theorem's hypothesis, not the spec's. -/
abbrev fiat_25519_to_bytes_spec (o q : Pointer) (s : GlobalState)
    (ho : IsByteBufPtr s.mem o) (hq : IsFieldElemPtr s.mem q) : Prop :=
  let invocation := runFunction (fiat_25519_to_bytes.denote
    (Ctxt.Valuation.ofHVector [.value q, .value o]ₕ))
  let result := StateT.run invocation s
  let q_input := readFieldElem hq

  ∃ out : BitVec 256,
    let output_state : GlobalState := { s with mem := s.mem.splice o out }

    readBuf (m := output_state.mem) (isByteBufPtr_splice ho)
        = BitVec.ofNat 256 q_input.val
    ∧ (∃ s' : GlobalState , result = .value ([]ₕ, s') ∧ output_state ≈ s')

end Firedancer.Ref

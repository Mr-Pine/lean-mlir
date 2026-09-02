import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_from_bytes
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `fiat_25519_from_bytes` deserialises the 32 little-endian bytes at `p` into
the five limbs at `o`. The buffer's top bit is masked off, so any 32 bytes are
accepted and the value is the low 255 bits reduced mod `p`. The result is tight. -/
abbrev fiat_25519_from_bytes_spec (o p: Pointer) (s: GlobalState)
    (ho : IsFieldElemPtr s.mem o) (hp : IsByteBufPtr s.mem p) : Prop :=
  let invocation := runFunction (fiat_25519_from_bytes.denote (Ctxt.Valuation.ofHVector [.value p, .value o]ₕ))
  let result := StateT.run invocation s
  let p_input := readBuf hp

  ∃ out : Fin 5 → BitVec 64,
    let output_state : GlobalState := { s with mem := s.mem.splice o (packLimbs out) }

    readFieldElem (m := output_state.mem) (isFieldElemPtr_splice ho) = decodeBytes p_input
    ∧ LimbBounds (m := output_state.mem) (isFieldElemPtr_splice ho)
    ∧ (∃ s' : GlobalState , result = .value ([]ₕ, s') ∧ output_state ≈ s')

end Firedancer.Ref

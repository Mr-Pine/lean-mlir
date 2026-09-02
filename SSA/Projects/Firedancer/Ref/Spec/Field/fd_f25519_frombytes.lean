import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_frombytes
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

abbrev fd_f25519_frombytes_spec (o p: Pointer) (s: GlobalState)
    (ho : IsFieldElemPtr s.mem o) (hp : IsByteBufPtr s.mem p) : Prop :=
  let invocation := runFunction (fd_f25519_frombytes.denote (Ctxt.Valuation.ofHVector [.value p, .value o]ₕ))
  let result := StateT.run invocation s
  let p_input := readBuf hp

  ∃ out : Fin 5 → BitVec 64,
    let output_state : GlobalState := { s with mem := s.mem.splice o (packLimbs out) }

    readFieldElem (m := output_state.mem) (isFieldElemPtr_splice ho) = decodeBytes p_input
    ∧ LimbBounds (m := output_state.mem) (isFieldElemPtr_splice ho)
    ∧ (∃ s' : GlobalState , result = .value ([.value o]ₕ, s') ∧ output_state ≈ s')

end Firedancer.Ref

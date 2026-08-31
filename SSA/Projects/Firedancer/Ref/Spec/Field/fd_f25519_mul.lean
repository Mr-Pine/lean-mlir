import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_mul
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

abbrev fd_f25519_mul_spec (o p q: Pointer) (s: GlobalState)
    (hp : IsFieldElemPtr s.mem p) (hq : IsFieldElemPtr s.mem q) : Prop :=
  let invocation := runFunction (fd_f25519_mul.denote (Ctxt.Valuation.ofHVector [.value q, .value p, .value o]ₕ))
  let result := StateT.run invocation s
  let p_input := readFieldElem p s.mem hp
  let q_input := readFieldElem q s.mem hq

  ∃ out : BitVec (5 * 64),
    let output_state : GlobalState := { s with mem := s.mem.splice o out }

    decodeFieldElem (fun i => (out.extractLsb' (64 * i.toNat) 64).toNat) = p_input * q_input
    ∧ (∃ s' : GlobalState , result = .value ([.value o]ₕ, s') ∧ output_state ≈ s')
    ∧ ∀ (i : Fin 5) (l : ℕ), readLimb? o i output_state.mem = some l → l ≤ 0x8000000000000

end Firedancer.Ref

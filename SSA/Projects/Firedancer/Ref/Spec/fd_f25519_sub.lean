import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.fd_f25519_sub
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

abbrev fd_f25519_sub_spec (o p q: Pointer) (s: GlobalState) : Prop :=
  let invocation := (fd_f25519_sub.denote (Ctxt.Valuation.ofHVector [.value q, .value p, .value o]ₕ ))
  let result := StateT.run invocation s
  let p_input := readFieldElem? p s.mem
  let q_input := readFieldElem? q s.mem

  ∃ out : BitVec (5 * 64),
    let output_state : GlobalState := { s with mem := s.mem.splice o out }

    (∃ s' : GlobalState , result = .value ([.value o]ₕ, s') ∧ output_state ≈ s')
    ∧ readFieldElem? o output_state.mem = Sub.sub <$> p_input <*> q_input
    ∧ ∀ (i : Fin 5) (l : ℕ), readLimb? o i output_state.mem = some l → l ≤ 0x8000000000000

end Firedancer.Ref

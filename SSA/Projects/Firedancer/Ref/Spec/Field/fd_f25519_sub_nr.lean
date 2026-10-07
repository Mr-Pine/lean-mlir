/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.SLLVM.Dialect
public import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_sub_nr
public import SSA.Projects.Firedancer.Ref.Spec.F25519

@[expose] public section

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `fiat_25519_sub_spec`, returning `o`: no carry, so the limbs are loose. -/
abbrev fd_f25519_sub_nr_spec (o p q : Pointer) (s : GlobalState) (ho : IsFieldElemPtr s.mem o)
    (hp : IsFieldElemPtr s.mem p) (hq : IsFieldElemPtr s.mem q) : Prop :=
  let invocation :=
    runFunction (fd_f25519_sub_nr.denote (Ctxt.Valuation.ofHVector [.value q, .value p, .value o]ₕ))
  let result := StateT.run invocation s
  let p_input := readFieldElem hp
  let q_input := readFieldElem hq
  ∃ out : BitVec (5 * 64),
    let output_state : GlobalState := { s with mem := s.mem.splice o out }
    readFieldElem (m := output_state.mem) (isFieldElemPtr_splice ho) = p_input - q_input ∧
      LimbBounds.Loose (m := output_state.mem) (isFieldElemPtr_splice ho) ∧
      (∃ s' : GlobalState, result = .value ([.value o]ₕ, s') ∧ output_state ≈ s')

end Firedancer.Ref

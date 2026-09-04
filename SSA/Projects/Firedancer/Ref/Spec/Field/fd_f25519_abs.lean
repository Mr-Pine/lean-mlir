/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_abs
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `o = ±a`, the representative whose canonical form is even. `fd_f25519_if`
copies out either `fd_f25519_neg`'s local or `a`, so the limbs keep
`fiat_25519_opp`'s bound; the input's tight bound is below it. -/
abbrev fd_f25519_abs_spec (o a : Pointer) (s : GlobalState)
    (ho : IsFieldElemPtr s.mem o) (ha : IsFieldElemPtr s.mem a) : Prop :=
  let invocation := runFunction (fd_f25519_abs.denote (Ctxt.Valuation.ofHVector [.value a, .value o]ₕ))
  let result := StateT.run invocation s
  let v := readFieldElem ha

  ∃ out : Fin 5 → BitVec 64,
    let output_state : GlobalState := { s with mem := s.mem.splice o (packLimbs out) }

    readFieldElem (m := output_state.mem) (isFieldElemPtr_splice ho)
        = (if v.val % 2 = 1 then -v else v)
    ∧ LimbBounds (m := output_state.mem) (isFieldElemPtr_splice ho) 0xffffffffffffe
    ∧ (∃ s' : GlobalState , result = .value ([.value o]ₕ, s') ∧ output_state ≈ s')

end Firedancer.Ref

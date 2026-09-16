/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_abs
import SSA.Projects.Firedancer.Ref.Spec.Bias

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `o = ±a`, the representative whose canonical form is even. `fd_f25519_if`
copies out either `fd_f25519_neg`'s local or `a`, so the limbs keep
`fiat_25519_opp`'s *per-limb* bound; the input's tight bound is below it.

The sum bound is the other half of what `fiat_25519_to_bytes` wants, and it is
not free: bias bounds alone give `limbSum ≤ 2 · p`, with equality exactly at
the all-maximal vector. The negate branch escapes it because `-a ≠ 0` there
(it is taken only when `a` is odd), the copy branch because `a` is tight. -/
abbrev fd_f25519_abs_spec (o a : Pointer) (s : GlobalState) (ho : IsFieldElemPtr s.mem o)
    (ha : IsFieldElemPtr s.mem a) : Prop :=
  let invocation :=
    runFunction (fd_f25519_abs.denote (Ctxt.Valuation.ofHVector [.value a, .value o]ₕ))
  let result := StateT.run invocation s
  let v := readFieldElem ha
  ∃ out : Fin 5 → BitVec 64,
    let output_state : GlobalState := { s with mem := s.mem.splice o (packLimbs out) }
    readFieldElem (m := output_state.mem) (isFieldElemPtr_splice ho) =
        (if v.val % 2 = 1 then -v else v) ∧
      BiasBounds (m := output_state.mem) (isFieldElemPtr_splice ho) ∧
      limbSum (m := output_state.mem) (isFieldElemPtr_splice ho) < 2 ^ 256 - 38 ∧
      (∃ s' : GlobalState, result = .value ([.value o]ₕ, s') ∧ output_state ≈ s')
      -- all-zero limbs come only from an all-zero `a`: `-a`'s never are
      ∧ (ZeroLimbs o output_state.mem → ZeroLimbs a s.mem)

end Firedancer.Ref

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_set_zero
public import SSA.Projects.Firedancer.Ref.Proof.RefWF
public import SSA.Projects.Firedancer.Ref.Spec.Point

@[expose] public section

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- `r = Point.zero`: `fd_f25519_set` copies `@fd_f25519_zero`, `@fd_f25519_one`,
`@fd_f25519_one`, `@fd_f25519_zero` into `X, Y, Z, T` (byte offsets 0, 40, 120, 80), so
the globals' tight bounds carry to `r`. `RefWF [r]` holds both globals apart from `r`, as
`fd_f25519_set` requires. -/
abbrev fd_ed25519_point_set_zero_spec (r : Pointer) (s : GlobalState) (hr : IsPointPtr s.mem r) :
    Prop :=
  let invocation :=
    runFunction (fd_ed25519_point_set_zero.denote (Ctxt.Valuation.singleton (.value r)))
  let result := StateT.run invocation s
  s.RefWF [r] →
    ∃ s' : GlobalState,
      result = .value ([.value r]ₕ, s') ∧
        ∃ oX oY oZ oT : BitVec (5 * 64),
          let outMem :=
            (((s.mem.splice r oX).splice (r.withOffset 40) oY).splice (r.withOffset 120) oZ).splice
              (r.withOffset 80) oT
          let output_state : GlobalState := { s with mem := outMem }
          have hpt : IsPointPtr outMem r :=
            isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hr)))
          output_state ≈ s' ∧ readPoint hpt = .zero ∧ AllLimbBounds hpt

end Firedancer.Ref

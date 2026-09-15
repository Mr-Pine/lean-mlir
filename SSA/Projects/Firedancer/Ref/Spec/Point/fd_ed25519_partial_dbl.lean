/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_partial_dbl
import SSA.Projects.Firedancer.Ref.Spec.Point
import SSA.Projects.Firedancer.Ref.Spec.Point.Dbl

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- `r = partialDbl a`, stored `T, Z, Y, X` (byte offsets 80, 120, 40, 0). `a`
is read only before the first store to `r`, so the two may overlap. `T` and `Z`
come out of carrying calls and are tight; `X` and `Y` are loose. -/
abbrev fd_ed25519_partial_dbl_spec (r a : Pointer) (s : GlobalState)
    (hr : IsPointPtr s.mem r) (ha : IsPointPtr s.mem a) : Prop :=
  let invocation := runFunction
    (fd_ed25519_partial_dbl.denote (Ctxt.Valuation.ofHVector [.value a, .value r]ₕ))
  let result := StateT.run invocation s

  ∃ oT oZ oY oX : BitVec (5 * 64),
    let outMem := (((s.mem.splice (r.withOffset 80) oT).splice (r.withOffset 120) oZ).splice
      (r.withOffset 40) oY).splice r oX
    let output_state : GlobalState := { s with mem := outMem }

    have hpt : IsPointPtr outMem r :=
      isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hr)))

    (∃ s' : GlobalState, result = .value ([.value r]ₕ, s') ∧ output_state ≈ s')
    ∧ readPoint hpt = (readPoint ha).partialDbl
    ∧ LimbBounds.Loose (isCoordPtr hpt 0) ∧ LimbBounds.Loose (isCoordPtr hpt 1)
    ∧ LimbBounds (isCoordPtr hpt 2) ∧ LimbBounds (isCoordPtr hpt 3)

end Firedancer.Ref

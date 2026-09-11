/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_set
import SSA.Projects.Firedancer.Ref.Spec.Point
import SSA.Projects.Firedancer.Ref.Proof.Point

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- `r = a`: four `fd_f25519_set`s in call order `X, Y, Z, T` (byte offsets 0,
40, 120, 80), limb for limb, so `a`'s limb bounds carry to `r`. `r` and `a` lie
in different blocks, as `fd_f25519_set` requires. -/
abbrev fd_ed25519_point_set_spec (r a : Pointer) (s : GlobalState)
    (_ : r.id ≠ a.id) (hr : IsPointPtr s.mem r) (ha : IsPointPtr s.mem a) : Prop :=
  let invocation := runFunction
    (fd_ed25519_point_set.denote (Ctxt.Valuation.ofHVector [.value a, .value r]ₕ))
  let result := StateT.run invocation s

  ∃ oX oY oZ oT : BitVec (5 * 64),
    let outMem := (((s.mem.splice r oX).splice (r.withOffset 40) oY).splice
      (r.withOffset 120) oZ).splice (r.withOffset 80) oT
    let output_state : GlobalState := { s with mem := outMem }

    have hpt : IsPointPtr outMem r :=
      isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hr)))

    (∃ s' : GlobalState, result = .value ([.value r]ₕ, s') ∧ output_state ≈ s')
    ∧ (∀ i : Fin 5, readLimb? r i outMem = readLimb? a i s.mem)
    ∧ (∀ i : Fin 5, readLimb? (r.withOffset 40) i outMem = readLimb? (a.withOffset 40) i s.mem)
    ∧ (∀ i : Fin 5, readLimb? (r.withOffset 80) i outMem = readLimb? (a.withOffset 80) i s.mem)
    ∧ (∀ i : Fin 5, readLimb? (r.withOffset 120) i outMem = readLimb? (a.withOffset 120) i s.mem)
    ∧ readPoint hpt = readPoint ha

end Firedancer.Ref

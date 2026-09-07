import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_from
import SSA.Projects.Firedancer.Ref.Spec.Point
import SSA.Projects.Firedancer.Ref.Proof.Point

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `r = (x : y : z : t)`: four `fd_f25519_set`s into the point's coordinates,
stated limb for limb like `fd_f25519_set_spec`, over the total `readLimb` --
which is why the four `IsFieldElemPtr` witnesses come in as hypotheses. The struct field order is
`X, Y, T, Z`, so `z` lands at byte offset 120 and `t` at 80 -- and the splice
chain mirrors the region's call order `X, Y, Z, T`. The block disjointness
carries over from `fd_f25519_set`: no coordinate source may live in `r`'s
block. -/
abbrev fd_ed25519_point_from_spec (r x y z t: Pointer) (s: GlobalState)
    (_ : x.id ≠ r.id) (_ : y.id ≠ r.id) (_ : z.id ≠ r.id) (_ : t.id ≠ r.id)
    (hr : IsPointPtr s.mem r)
    (hx : IsFieldElemPtr s.mem x) (hy : IsFieldElemPtr s.mem y)
    (hz : IsFieldElemPtr s.mem z) (ht : IsFieldElemPtr s.mem t) : Prop :=
  let invocation := runFunction
    (fd_ed25519_point_from.denote (Ctxt.Valuation.ofHVector
      [.value t, .value z, .value y, .value x, .value r]ₕ))
  let result := StateT.run invocation s

  ∃ oX oY oZ oT : BitVec (5 * 64),
    let outMem := (((s.mem.splice r oX).splice (r.withOffset 40) oY).splice
      (r.withOffset 120) oZ).splice (r.withOffset 80) oT
    let output_state : GlobalState := { s with mem := outMem }

    have hpt : IsPointPtr outMem r :=
      isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hr)))
    have hoX : IsFieldElemPtr outMem r := coordPtr_zero r ▸ isCoordPtr hpt 0
    have hoY : IsFieldElemPtr outMem (r.withOffset 40) := coordPtr_one r ▸ isCoordPtr hpt 1
    have hoT : IsFieldElemPtr outMem (r.withOffset 80) := coordPtr_two r ▸ isCoordPtr hpt 2
    have hoZ : IsFieldElemPtr outMem (r.withOffset 120) := coordPtr_three r ▸ isCoordPtr hpt 3

    (∃ s' : GlobalState , result = .value ([.value r]ₕ, s') ∧ output_state ≈ s')
    ∧ (∀ i : Fin 5, readLimb i hoX = readLimb i hx)
    ∧ (∀ i : Fin 5, readLimb i hoY = readLimb i hy)
    ∧ (∀ i : Fin 5, readLimb i hoT = readLimb i ht)
    ∧ (∀ i : Fin 5, readLimb i hoZ = readLimb i hz)

end Firedancer.Ref

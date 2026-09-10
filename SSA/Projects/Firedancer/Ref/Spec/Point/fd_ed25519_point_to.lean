/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_to
import SSA.Projects.Firedancer.Ref.Spec.Point
import SSA.Projects.Firedancer.Ref.Proof.Point

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- `(x, y, z, t) = a`: four `fd_f25519_set`s out of the point's coordinates,
the inverse of `fd_ed25519_point_from`. The struct field order is `X, Y, T, Z`,
so `z` reads byte offset 120 and `t` reads 80, while the splice chain follows
the region's call order `x, y, z, t`.

Stated limb for limb as well as value for value: `fd_f25519_set` copies limbs
verbatim, so whatever bounds the coordinates satisfied carry to the outputs.
Both are over the total `readLimb`/`readFieldElem`, as in
`fd_ed25519_point_from_spec` -- which is why the four destination
`IsFieldElemPtr` witnesses come in as hypotheses.

`hNodup` is stronger than `fd_f25519_set`'s block disjointness on purpose. The
region copies one coordinate at a time, so a destination sharing `a`'s block
could corrupt a later copy's input, and two destinations sharing a block would
clobber each other. -/
abbrev fd_ed25519_point_to_spec (x y z t a : Pointer) (s : GlobalState)
    (_hNodup : ([x, y, z, t, a].map Pointer.id).Nodup)
    (ha : IsPointPtr s.mem a)
    (hx : IsFieldElemPtr s.mem x) (hy : IsFieldElemPtr s.mem y)
    (hz : IsFieldElemPtr s.mem z) (ht : IsFieldElemPtr s.mem t) : Prop :=
  let invocation := runFunction
    (fd_ed25519_point_to.denote (Ctxt.Valuation.ofHVector
      [.value a, .value t, .value z, .value y, .value x]ₕ))
  let result := StateT.run invocation s
  let P := readPoint ha

  -- The four coordinates of `a`, at the offsets the region's `getelementptr`s
  -- compute: `Z` is field 3 and `T` field 2.
  have haX : IsFieldElemPtr s.mem a := coordPtr_zero a ▸ isCoordPtr ha 0
  have haY : IsFieldElemPtr s.mem (a.withOffset 40) := coordPtr_one a ▸ isCoordPtr ha 1
  have haT : IsFieldElemPtr s.mem (a.withOffset 80) := coordPtr_two a ▸ isCoordPtr ha 2
  have haZ : IsFieldElemPtr s.mem (a.withOffset 120) := coordPtr_three a ▸ isCoordPtr ha 3

  ∃ oX oY oZ oT : BitVec (5 * 64),
    let outMem := (((s.mem.splice x oX).splice y oY).splice z oZ).splice t oT
    let output_state : GlobalState := { s with mem := outMem }

    have hoX : IsFieldElemPtr outMem x :=
      isFieldElemPtr_splice (isFieldElemPtr_splice
        (isFieldElemPtr_splice (isFieldElemPtr_splice hx)))
    have hoY : IsFieldElemPtr outMem y :=
      isFieldElemPtr_splice (isFieldElemPtr_splice
        (isFieldElemPtr_splice (isFieldElemPtr_splice hy)))
    have hoZ : IsFieldElemPtr outMem z :=
      isFieldElemPtr_splice (isFieldElemPtr_splice
        (isFieldElemPtr_splice (isFieldElemPtr_splice hz)))
    have hoT : IsFieldElemPtr outMem t :=
      isFieldElemPtr_splice (isFieldElemPtr_splice
        (isFieldElemPtr_splice (isFieldElemPtr_splice ht)))

    (∃ s' : GlobalState, result = .value ([]ₕ, s') ∧ output_state ≈ s')
    ∧ (∀ i : Fin 5, readLimb i hoX = readLimb i haX)
    ∧ (∀ i : Fin 5, readLimb i hoY = readLimb i haY)
    ∧ (∀ i : Fin 5, readLimb i hoZ = readLimb i haZ)
    ∧ (∀ i : Fin 5, readLimb i hoT = readLimb i haT)
    ∧ readFieldElem hoX = P.X
    ∧ readFieldElem hoY = P.Y
    ∧ readFieldElem hoZ = P.Z
    ∧ readFieldElem hoT = P.T

end Firedancer.Ref

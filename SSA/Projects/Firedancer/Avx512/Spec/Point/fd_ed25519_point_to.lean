/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_to
import SSA.Projects.Firedancer.Avx512.Spec.Vec
import SSA.Projects.Firedancer.Curve

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- A QUAD element's six limbs as an `fd_r43x6_t`: lanes 6 and 7 zeroed. -/
def widenVec (v : Vector (BitVec 64) 6) : Vector (BitVec 64) 8 :=
  #v[v[0], v[1], v[2], v[3], v[4], v[5], 0#64, 0#64]

/-- Padding does not move the value: `decodeVec` only reads lanes 0-5. -/
@[simp] theorem vecValue_widenVec (v : Vector (BitVec 64) 6) :
    vecValue (widenVec v) = decodeVec (le_refl 6) v := by
  simp [vecValue, decodeVec, widenVec]

/-- Stated over the total `readVec`, like `Ref.fd_ed25519_point_from_spec` is
over `readLimb` -- which is why the four `IsVecPtr` witnesses come in as
hypotheses, and are pushed through the four stores by `isVecPtr_splice`. -/
abbrev fd_ed25519_point_to_spec (x y z t a : Pointer) (s : GlobalState)
    (_hNodup : ([x, y, z, t].map Pointer.id).Nodup)
    (ha : IsQuadPtr s.mem a)
    (hx : IsVecPtr s.mem x) (hy : IsVecPtr s.mem y)
    (hz : IsVecPtr s.mem z) (ht : IsVecPtr s.mem t) : Prop :=
  let invocation := runFunction
    (fd_ed25519_point_to.denote (Ctxt.Valuation.ofHVector
      [.value a, .value t, .value z, .value y, .value x]ₕ))
  let result := StateT.run invocation s
  let q := readQuad ha
  let V := q.PointVecs

  let outMem :=
    (((s.mem.splice x (vecBV (widenVec V.X))).splice y (vecBV (widenVec V.Y))).splice
      z (vecBV (widenVec V.Z))).splice t (vecBV (widenVec V.T))
  let output_state : GlobalState := { s with mem := outMem }

  have hoX : IsVecPtr outMem x :=
    isVecPtr_splice (isVecPtr_splice (isVecPtr_splice (isVecPtr_splice hx)))
  have hoY : IsVecPtr outMem y :=
    isVecPtr_splice (isVecPtr_splice (isVecPtr_splice (isVecPtr_splice hy)))
  have hoZ : IsVecPtr outMem z :=
    isVecPtr_splice (isVecPtr_splice (isVecPtr_splice (isVecPtr_splice hz)))
  have hoT : IsVecPtr outMem t :=
    isVecPtr_splice (isVecPtr_splice (isVecPtr_splice (isVecPtr_splice ht)))

  (∃ s' : GlobalState, result = .value ([]ₕ, s') ∧ output_state ≈ s')
  ∧ readVec hoX = widenVec V.X
  ∧ readVec hoY = widenVec V.Y
  ∧ readVec hoZ = widenVec V.Z
  ∧ readVec hoT = widenVec V.T
  ∧ vecValue (readVec hoX) = q.toPoint.X
  ∧ vecValue (readVec hoY) = q.toPoint.Y
  ∧ vecValue (readVec hoZ) = q.toPoint.Z
  ∧ vecValue (readVec hoT) = q.toPoint.T

end Firedancer.Avx512

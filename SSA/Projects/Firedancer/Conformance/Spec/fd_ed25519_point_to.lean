/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_to
import SSA.Projects.Firedancer.Ref.Spec.Point
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_to
import SSA.Projects.Firedancer.Avx512.Spec.Vec
import SSA.Projects.Firedancer.Curve

/-!
# `fd_ed25519_point_to`: ref ≡ avx512

The input relation is coordinate-wise *equality*, not `Point.SamePoint`: this
operation exposes the raw projective coordinates, so `(X, Y, Z, T)` and
`(2X, 2Y, 2Z, 2T)` -- the same point -- give different answers.

The two aliasing hypotheses differ, and that asymmetry is real. ref copies one
coordinate at a time, so a destination overlapping the source would have the
first copy corrupt the second's input: `hNodup` covers `a` as well. avx512
loads all three QUAD vectors before its first store, so only the four
destinations have to be pairwise apart -- `a'` may alias one of them.

The region returns void, so memory is the whole observable, and each side's
final state is pinned to a splice chain in program order -- four 320-bit
stores for ref, four 512-bit whole-vector stores for avx512.
Stating it that way subsumes a frame condition: the memory *is* the initial
one with exactly those four splices, so nothing else can have moved. The
per-store `packLimbs`/`vecBV` shape is the same aggregate reading
`Ref.pointOutMem` and `MemoryState.writeQuad` take in the `frombytes_2x`
specs; ref's `fd_f25519_set` copies limb by limb, and the five splices are
proved equal to the one.
-/

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

abbrev fd_ed25519_point_to_equivalent : Prop :=
  ∀ (s : GlobalState) (x y z t a : Pointer),
  (hs : s.WF) →
  (ha : Ref.IsPointPtr s.mem a) →
  (hx : Ref.IsFieldElemPtr s.mem x) → (hy : Ref.IsFieldElemPtr s.mem y) →
  (hz : Ref.IsFieldElemPtr s.mem z) → (ht : Ref.IsFieldElemPtr s.mem t) →
  (hNodup : ([x, y, z, t, a].map Pointer.id).Nodup) →

  let refResult := StateT.run (runFunction (Ref.fd_ed25519_point_to.denote
    (Ctxt.Valuation.ofHVector [.value a, .value t, .value z, .value y, .value x]ₕ))) s

  ∀ (s' : GlobalState) (x' y' z' t' a' : Pointer),
  (hs' : s'.WF) →
  (ha' : Avx512.IsQuadPtr s'.mem a') →
  (hx' : Avx512.IsVecPtr s'.mem x') → (hy' : Avx512.IsVecPtr s'.mem y') →
  (hz' : Avx512.IsVecPtr s'.mem z') → (ht' : Avx512.IsVecPtr s'.mem t') →
  (hNodup' : ([x', y', z', t'].map Pointer.id).Nodup) →

  let avxResult := StateT.run (runFunction (Avx512.fd_ed25519_point_to.denote
    (Ctxt.Valuation.ofHVector [.value a', .value t', .value z', .value y', .value x']ₕ))) s'

  -- The two backends hold the *same* representation of the point, not merely
  -- two representations of the same point.
  Ref.readPoint ha = (Avx512.readQuad ha').toPoint →

  ∃ (refOut : _) (avxOut : _)
    (_href : refResult = .value refOut) (_havx : avxResult = .value avxOut)
    (oX oY oZ oT : BitVec (5 * 64))
    (vX vY vZ vT : Vector (BitVec 64) 8),

    -- The four stores each region makes, in program order.
    let refMem := (((s.mem.splice x oX).splice y oY).splice z oZ).splice t oT
    let avxMem := (((s'.mem.splice x' (Avx512.vecBV vX)).splice y' (Avx512.vecBV vY)).splice z'
      (Avx512.vecBV vZ)).splice t' (Avx512.vecBV vT)

    ∃ (_hrefMem : refOut.snd ≈ { s with mem := refMem })
      (_havxMem : avxOut.snd ≈ { s' with mem := avxMem })
      (hxOut : Ref.IsFieldElemPtr refMem x) (hyOut : Ref.IsFieldElemPtr refMem y)
      (hzOut : Ref.IsFieldElemPtr refMem z) (htOut : Ref.IsFieldElemPtr refMem t)
      (hxOut' : Avx512.IsVecPtr avxMem x') (hyOut' : Avx512.IsVecPtr avxMem y')
      (hzOut' : Avx512.IsVecPtr avxMem z') (htOut' : Avx512.IsVecPtr avxMem t'),

      let P := Ref.readPoint ha

      (Ref.readFieldElem hxOut = Avx512.vecValue (Avx512.readVec hxOut')
        ∧ Ref.readFieldElem hxOut = P.X) ∧
      (Ref.readFieldElem hyOut = Avx512.vecValue (Avx512.readVec hyOut')
        ∧ Ref.readFieldElem hyOut = P.Y) ∧
      (Ref.readFieldElem hzOut = Avx512.vecValue (Avx512.readVec hzOut')
        ∧ Ref.readFieldElem hzOut = P.Z) ∧
      (Ref.readFieldElem htOut = Avx512.vecValue (Avx512.readVec htOut')
        ∧ Ref.readFieldElem htOut = P.T)

end Firedancer

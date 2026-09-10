/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Conformance.Spec.fd_ed25519_point_to
import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_point_to
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_to

/-!
# `fd_ed25519_point_to`: ref ≡ avx512

Both halves already say where their four stores land and what reads back out
of them, each in its own representation. All that is left is to put the two
readbacks beside each other: the hypothesis relates the two *inputs*
coordinate for coordinate, and each side's conformance relates its outputs to
its own input, so the outputs agree by transitivity.

The avx512 region loads all three QUAD vectors before its first store, so its
spec asks only that the four destinations be pairwise distinct; the ref one
also needs them apart from `a`. Each side's hypothesis is stated as that
backend needs it, so both conformance theorems apply directly.
-/

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

set_option maxHeartbeats 1000000 in
theorem fd_ed25519_point_to : fd_ed25519_point_to_equivalent := by
  unfold fd_ed25519_point_to_equivalent
  intro s x y z t a hs ha hx hy hz ht hNodup refResult

  obtain ⟨oX, oY, oZ, oT, ⟨sRef, hrefRun, hrefEq⟩, -, -, -, -, hvX, hvY, hvZ, hvT⟩ :=
    Ref.fd_ed25519_point_to_conforms x y z t a s hs hNodup ha hx hy hz ht

  intro s' x' y' z' t' a' hs' ha' hx' hy' hz' ht' hNodup' avxResult

  obtain ⟨⟨sAvx, havxRun, havxEq⟩, -, -, -, -, hwX, hwY, hwZ, hwT⟩ :=
    Avx512.fd_ed25519_point_to_conforms x' y' z' t' a' s' hs' hNodup' ha' hx' hy' hz' ht'

  intro hlink

  refine ⟨(_, sRef), (_, sAvx), hrefRun, havxRun, oX, oY, oZ, oT,
    Avx512.widenVec (Avx512.readQuad ha').PointVecs.X,
    Avx512.widenVec (Avx512.readQuad ha').PointVecs.Y,
    Avx512.widenVec (Avx512.readQuad ha').PointVecs.Z,
    Avx512.widenVec (Avx512.readQuad ha').PointVecs.T,
    GlobalState.Equiv.symm hrefEq, GlobalState.Equiv.symm havxEq,
    Ref.isFieldElemPtr_splice (Ref.isFieldElemPtr_splice
      (Ref.isFieldElemPtr_splice (Ref.isFieldElemPtr_splice hx))),
    Ref.isFieldElemPtr_splice (Ref.isFieldElemPtr_splice
      (Ref.isFieldElemPtr_splice (Ref.isFieldElemPtr_splice hy))),
    Ref.isFieldElemPtr_splice (Ref.isFieldElemPtr_splice
      (Ref.isFieldElemPtr_splice (Ref.isFieldElemPtr_splice hz))),
    Ref.isFieldElemPtr_splice (Ref.isFieldElemPtr_splice
      (Ref.isFieldElemPtr_splice (Ref.isFieldElemPtr_splice ht))),
    Avx512.isVecPtr_splice (Avx512.isVecPtr_splice
      (Avx512.isVecPtr_splice (Avx512.isVecPtr_splice hx'))),
    Avx512.isVecPtr_splice (Avx512.isVecPtr_splice
      (Avx512.isVecPtr_splice (Avx512.isVecPtr_splice hy'))),
    Avx512.isVecPtr_splice (Avx512.isVecPtr_splice
      (Avx512.isVecPtr_splice (Avx512.isVecPtr_splice hz'))),
    Avx512.isVecPtr_splice (Avx512.isVecPtr_splice
      (Avx512.isVecPtr_splice (Avx512.isVecPtr_splice ht'))),
    ⟨?_, hvX⟩, ⟨?_, hvY⟩, ⟨?_, hvZ⟩, ⟨?_, hvT⟩⟩

  -- Each: ref output = that coordinate of the ref point = the same coordinate
  -- of the avx512 point (`hlink`) = avx512 output.
  · rw [hvX, hwX, hlink]
  · rw [hvY, hwY, hlink]
  · rw [hvZ, hwZ, hlink]
  · rw [hvT, hwT, hlink]

end Firedancer

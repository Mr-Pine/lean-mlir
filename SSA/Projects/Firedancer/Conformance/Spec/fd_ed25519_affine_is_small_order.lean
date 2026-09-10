/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_affine_is_small_order
import SSA.Projects.Firedancer.Ref.Spec.Point
import SSA.Projects.Firedancer.Ref.Spec.Bias
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_affine_is_small_order
import SSA.Projects.Firedancer.Avx512.Spec.Quad
import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_to
import SSA.Projects.Firedancer.Avx512.Spec.Vec
import SSA.Projects.Firedancer.Conformance.Spec.Order8
import SSA.Projects.Firedancer.Proof.Globals
import SSA.Projects.Firedancer.Curve

/-!
# `fd_ed25519_affine_is_small_order`: ref ≡ avx512

Both backends compile the *same* source -- the shared `fd_curve25519.h` inline,
not `fd_r43x6_ge_is_small_order`, which does three doublings and is never
reached here. The two regions agree op for op: copy the point out with
`fd_ed25519_point_to`, then `X == 0 | Y == 0 | Y == y0 | Y == y1`.

So this is the first conformance statement whose proof is a *relational walk*
rather than a composition of two whole-function specifications: there is no
arithmetic in the region to specify, only nine calls and the invariant tying
the two states together. See `Conformance/Rel.lean` for `Corr`, which is what
the proof carries; it deliberately does not appear here, because the statement
is the same shape as every other conformance statement in this directory.

## What the statement assumes, and why

* the argument point, related across the backends coordinate for coordinate --
  `readPoint = readQuad.toPoint`, equality of representations rather than
  `SamePoint`, because `fd_ed25519_point_to` exposes the raw projective
  coordinates;
* the two order-8 globals, at whatever addresses each state records, holding
  the same field element on both sides. `Conformance/Spec/Order8.lean` is where
  that is discharged for the artifacts' own initialisers -- the two encodings
  denote equal naturals, both already reduced;
* per-side bounds the callees need. The alloca'd copies inherit them from the
  argument, because `fd_ed25519_point_to` is a verbatim coordinate copy on both
  sides (its spec states exactly that), so nothing further is assumed of them.

No disjointness between the globals and the region's four allocas is assumed:
`HoldsGlobal.lt_nextFreeBlock` puts a global's block below `nextFreeBlock`, and
the allocas come from above it.

## What is deliberately *not* claimed

That the predicate detects order ≤ 8. That is only true for an affine point
(`Z == 1`; see the comment at `fd_curve25519.h:105`) and needs the
classification of the eight low-order points. Conformance needs none of it, and
the functional theorem is a separate, ref-side-only artifact if it is ever
wanted. Recorded in `LIMITATIONS.md`.
-/

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

abbrev fd_ed25519_affine_is_small_order_equivalent : Prop :=
  ∀ (s : GlobalState) (a g0 g1 : Pointer),
  (hs : s.WF) → (ha : Ref.IsPointPtr s.mem a) → (haLimbs : Ref.AllLimbBounds ha) →
  (hg0 : GlobalPtr s "fd_ed25519_order8_point_y0" g0) →
  (hg1 : GlobalPtr s "fd_ed25519_order8_point_y1" g1) →
  (hg0f : Ref.IsFieldElemPtr s.mem g0) → (hg1f : Ref.IsFieldElemPtr s.mem g1) →
  (hg0b : Ref.BiasBounds hg0f) → (hg1b : Ref.BiasBounds hg1f) →
  -- The two globals are distinct blocks. `Proof/Globals.lean` deliberately does
  -- not give this -- LLVM lets globals overlap (`unnamed_addr`, `@alias`) -- so
  -- a spec that needs it says so; the loader supplies it for a module loaded
  -- from scratch, one block per symbol.
  (hgne : g0.id ≠ g1.id) →

  let refResult := StateT.run (runFunction
    (Ref.fd_ed25519_affine_is_small_order.denote (Ctxt.Valuation.singleton (.value a)))) s

  ∀ (s' : GlobalState) (a' g0' g1' : Pointer),
  (hs' : s'.WF) → (ha' : Avx512.IsQuadPtr s'.mem a') →
  -- The callees' preconditions on the copied coordinates: `fd_f25519_is_zero`
  -- needs `NearlyReduced` on `x` and `y`, `fd_f25519_eq` needs `Reduced` on `y`.
  -- Stated on the coordinate vectors as `fd_ed25519_point_to` lays them out
  -- (`widenVec`, lanes 6-7 clear). `Quad.U46` would be both the wrong shape --
  -- it bounds the interleaved `v03/v14/v25` -- and, at 2^46, too loose.
  (hXr : R43x6.Reduced (Avx512.widenVec (Avx512.readQuad ha').PointVecs.X)) →
  (hYr : R43x6.Reduced (Avx512.widenVec (Avx512.readQuad ha').PointVecs.Y)) →
  (hg0' : GlobalPtr s' "fd_ed25519_order8_point_y0" g0') →
  (hg1' : GlobalPtr s' "fd_ed25519_order8_point_y1" g1') →
  (hg0f' : Avx512.IsVecPtr s'.mem g0') → (hg1f' : Avx512.IsVecPtr s'.mem g1') →
  (hg0r : R43x6.Reduced (Avx512.readVec hg0f')) →
  (hg1r : R43x6.Reduced (Avx512.readVec hg1f')) →
  (hgne' : g0'.id ≠ g1'.id) →

  let avxResult := StateT.run (runFunction
    (Avx512.fd_ed25519_affine_is_small_order.denote (Ctxt.Valuation.singleton (.value a')))) s'

  -- The point, coordinate for coordinate.
  Ref.readPoint ha = (Avx512.readQuad ha').toPoint →
  -- The two globals, as field elements rather than as bytes.
  Ref.readFieldElem hg0f = Avx512.vecValue (Avx512.readVec hg0f') →
  Ref.readFieldElem hg1f = Avx512.vecValue (Avx512.readVec hg1f') →

  ∃ (r : BitVec 32) (sOut sOut' : GlobalState),
    refResult = .value ([(PoisonOr.value r : LLVM.IntW 32)]ₕ, sOut) ∧
    avxResult = .value ([(PoisonOr.value r : LLVM.IntW 32)]ₕ, sOut') ∧
    s ≈ sOut ∧ s' ≈ sOut'

end Firedancer

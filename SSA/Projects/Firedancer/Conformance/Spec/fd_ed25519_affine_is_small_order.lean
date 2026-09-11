/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_affine_is_small_order
import SSA.Projects.Firedancer.Ref.Spec.Point
import SSA.Projects.Firedancer.Ref.Proof.RefWF
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_affine_is_small_order
import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_to
import SSA.Projects.Firedancer.Avx512.Spec.Vec
import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_affine_is_small_order
import SSA.Projects.Firedancer.Proof.Globals

/-!
# `fd_ed25519_affine_is_small_order`: ref ≡ avx512

Both backends compile the same source -- the shared `fd_curve25519.h` inline --
so this is stated and proved *relationally*: the two regions are walked in
lockstep and shown to return the same `i32`, without either side's functional
specification. What the `i32` means is not this statement's business; the
per-backend specifications say that (`(P.X, P.Y) ∈ lowOrder`, under `Z = 1` and
the curve equation), and this one needs neither hypothesis: the two sides have
to *agree*, not decide anything.

The input relation is coordinate-wise equality of the two points, as for
`fd_ed25519_point_to`, the copy the region begins with. The remaining
hypotheses are exactly what the callees ask of their operands on each side, in
the form each backend's own specification uses: `RefWF` for the ref globals and
the argument's `AllLimbBounds`; on AVX-512 the two globals pointer by pointer,
and reducedness per slot in the `widenVec` layout `fd_ed25519_point_to` writes.
-/

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

abbrev fd_ed25519_affine_is_small_order_equivalent : Prop :=
  ∀ (s : GlobalState) (a : Pointer),
  (hrefwf : s.RefWF []) → (ha : Ref.IsPointPtr s.mem a) → (haLimbs : Ref.AllLimbBounds ha) →

  let refResult := StateT.run (runFunction
    (Ref.fd_ed25519_affine_is_small_order.denote (Ctxt.Valuation.singleton (.value a)))) s

  ∀ (s' : GlobalState) (a' g0' g1' : Pointer),
  (hs' : s'.WF) → (ha' : Avx512.IsQuadPtr s'.mem a') →
  (hg0' : Avx512.IsVecPtr s'.mem g0') → (hg1' : Avx512.IsVecPtr s'.mem g1') →
  GlobalPtr s' "fd_ed25519_order8_point_y0" g0' →
  GlobalPtr s' "fd_ed25519_order8_point_y1" g1' →
  Avx512.vecValue (Avx512.readVec hg0') = order8_y0 →
  Avx512.vecValue (Avx512.readVec hg1') = order8_y1 →
  R43x6.Reduced (Avx512.readVec hg0') → R43x6.Reduced (Avx512.readVec hg1') →
  R43x6.Reduced (Avx512.widenVec (Avx512.readQuad ha').PointVecs.X) →
  R43x6.Reduced (Avx512.widenVec (Avx512.readQuad ha').PointVecs.Y) →

  let avxResult := StateT.run (runFunction
    (Avx512.fd_ed25519_affine_is_small_order.denote (Ctxt.Valuation.singleton (.value a')))) s'

  -- The two backends hold the *same* representation of the point.
  Ref.readPoint ha = (Avx512.readQuad ha').toPoint →

  ∃ (r : BitVec 32) (sOut sOut' : GlobalState),
    refResult = .value ([(PoisonOr.value r : LLVM.IntW 32)]ₕ, sOut) ∧
    avxResult = .value ([(PoisonOr.value r : LLVM.IntW 32)]ₕ, sOut') ∧
    s ≈ sOut ∧ s' ≈ sOut'

end Firedancer

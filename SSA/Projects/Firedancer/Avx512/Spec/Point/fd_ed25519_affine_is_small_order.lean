/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_affine_is_small_order
import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_to
import SSA.Projects.Firedancer.Avx512.Spec.Vec
import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_f25519_is_zero
import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_affine_is_small_order
import SSA.Projects.Firedancer.Proof.Globals

/-!
# `fd_ed25519_affine_is_small_order` (AVX-512)

The same source as the ref region -- the `fd_curve25519.h` inline, not
`fd_r43x6_ge_is_small_order` -- so the same statement, with the field
representation swapped: a `FD_R43X6_QUAD` argument, `vector<8xi64>` globals, and
the value of a slot read by `vecValue` rather than `readFieldElem`.

The predicate is membership in the shared `lowOrder`, applied to the point the
QUAD holds. That is what makes this spec and the ref one comparable at all: both
say the region indicates the same thing about the same element of `ZMod p`, and
only the decoding differs. As on the ref side, `Z = 1` and the curve equation are
what turn the disjunction the region computes into that membership.

The two globals stay explicit arguments here, unlike on the ref side, where
they are part of `RefWF`. There is no AVX-512 counterpart to `RefWF` yet, so
what the module loads is said pointer by pointer; if one appears, these four
hypotheses are what it should absorb.

The bounds are per slot, and as loose as the two tests allow: `X` as a fold
leaves it, `Y` a 255-bit unpack that may be `p` or more -- what
`fd_r43x6_ge_decode2` hands back. Both make the only zeros `fd_f25519_is_zero`
can see its two bit patterns; `Y`'s 255 bits and the globals' reducedness make
`fd_f25519_eq`'s pattern test exact, as neither order-8 `y` is below `19`.
`fd_ed25519_point_to` writes each slot as `widenVec` of the QUAD's vector,
zeroing lanes 6 and 7. `Z` and `T` are written and never read back, so no bound
on them is needed.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

abbrev fd_ed25519_affine_is_small_order_spec (a g0 g1 : Pointer) (s : GlobalState)
    (ha : IsQuadPtr s.mem a)
    (hg0 : IsVecPtr s.mem g0) (hg1 : IsVecPtr s.mem g1) : Prop :=
  let invocation := runFunction
    (fd_ed25519_affine_is_small_order.denote (Ctxt.Valuation.singleton (.value a)))
  let result := StateT.run invocation s
  let q := readQuad ha
  let P := q.toPoint
  let output_value : LLVM.IntW _ := .value (if (P.X, P.Y) ∈ lowOrder then 1#32 else 0#32)

  P.Z = 1 → OnCurve P.x P.y →
  GlobalPtr s "fd_ed25519_order8_point_y0" g0 →
  GlobalPtr s "fd_ed25519_order8_point_y1" g1 →
  vecValue (readVec hg0) = order8_y0 →
  vecValue (readVec hg1) = order8_y1 →
  R43x6.Reduced (readVec hg0) → R43x6.Reduced (readVec hg1) →
  R43x6.Folded (widenVec q.PointVecs.X) → R43x6.Bits255 (widenVec q.PointVecs.Y) →
    ∃ s' : GlobalState, result = .value ([output_value]ₕ, s') ∧ s ≈ s'

end Firedancer.Avx512

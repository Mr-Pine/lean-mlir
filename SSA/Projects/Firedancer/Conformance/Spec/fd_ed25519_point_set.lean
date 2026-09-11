/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_set
import SSA.Projects.Firedancer.Ref.Spec.Point
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_set
import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_frombytes_2x

/-!
# `fd_ed25519_point_set`: ref ≡ avx512

The input relation is equality of the four coordinates, as for
`fd_ed25519_point_to`: a copy exposes the representation.
-/

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

abbrev fd_ed25519_point_set_equivalent : Prop :=
  ∀ (s : GlobalState) (r a : Pointer),
  (hs : s.WF) →
  (hr : Ref.IsPointPtr s.mem r) → (ha : Ref.IsPointPtr s.mem a) →
  (hne : r.id ≠ a.id) →

  let refResult := StateT.run (runFunction (Ref.fd_ed25519_point_set.denote
    (Ctxt.Valuation.ofHVector [.value a, .value r]ₕ))) s

  ∀ (s' : GlobalState) (r' a' : Pointer),
  (hs' : s'.WF) →
  (hr' : Avx512.IsQuadPtr s'.mem r') → (ha' : Avx512.IsQuadPtr s'.mem a') →
  (hne' : r'.id ≠ a'.id) →

  let avxResult := StateT.run (runFunction (Avx512.fd_ed25519_point_set.denote
    (Ctxt.Valuation.ofHVector [.value a', .value r']ₕ))) s'

  Ref.readPoint ha = (Avx512.readQuad ha').toPoint →

  ∃ (refOut : _) (avxOut : _)
    (_href : refResult = .value refOut) (_havx : avxResult = .value avxOut)
    (oX oY oZ oT : BitVec (5 * 64)) (q : Avx512.Quad),

    let refMem := (((s.mem.splice r oX).splice (r.withOffset 40) oY).splice
      (r.withOffset 120) oZ).splice (r.withOffset 80) oT
    let avxMem := s'.mem.writeQuad r' q

    ∃ (_hrefMem : refOut.snd ≈ { s with mem := refMem })
      (_havxMem : avxOut.snd ≈ { s' with mem := avxMem })
      (hrOut : Ref.IsPointPtr refMem r) (hrOut' : Avx512.IsQuadPtr avxMem r'),

      refOut.fst = [.value r]ₕ ∧ avxOut.fst = [.value r']ₕ
      ∧ Ref.readPoint hrOut = (Avx512.readQuad hrOut').toPoint
      ∧ Ref.readPoint hrOut = Ref.readPoint ha

end Firedancer

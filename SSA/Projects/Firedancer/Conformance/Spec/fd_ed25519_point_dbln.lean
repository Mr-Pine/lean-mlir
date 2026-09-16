/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_dbln
import SSA.Projects.Firedancer.Ref.Spec.Point
import SSA.Projects.Firedancer.Ref.Spec.Bias
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_dbln
import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_frombytes_2x
import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_point_dbln

/-!
# `fd_ed25519_point_dbln`: ref ≡ avx512

Both backends double with the same formulas, so the outputs agree coordinate
for coordinate, not merely as points; neither reads `T`, so the inputs need
only agree on `X`, `Y`, `Z`.

Each side's bounds are the ones its callees need: ref's `fd_f25519_add_nr`
takes a bias-bounded `X` and tight `Y`, and its `fd_f25519_sqr` a loose `Z`;
avx512 takes `u44` lanes. `n < 256` because the `uchar` counter wraps at 256 and the loop then
never exits.
-/

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

abbrev fd_ed25519_point_dbln_equivalent : Prop :=
  ∀ (s : GlobalState) (r a : Pointer) (n : BitVec 32),
  (hs : s.WF) →
  (hr : Ref.IsPointPtr s.mem r) → (ha : Ref.IsPointPtr s.mem a) →
  (haX : Ref.BiasBounds? a s.mem) →
  (haY : ∀ (i : Fin 5) (l : ℕ),
    Ref.readLimb? (a.withOffset 40) i s.mem = some l → l ≤ 0x8000000000000) →
  (haZ : ∀ (i : Fin 5) (l : ℕ),
    Ref.readLimb? (a.withOffset 120) i s.mem = some l → l ≤ 0x18000000000000) →
  (hn : n.toInt < 256) →

  let refResult := StateT.run (runFunction (Ref.fd_ed25519_point_dbln.denote
    (Ctxt.Valuation.ofHVector [.value n, .value a, .value r]ₕ))) s

  ∀ (s' : GlobalState) (r' a' : Pointer),
  (hs' : s'.WF) →
  (hr' : Avx512.IsQuadPtr s'.mem r') → (ha' : Avx512.IsQuadPtr s'.mem a') →
  (hu' : R43x6.U44 (Avx512.readQuad ha').v03 ∧ R43x6.U44 (Avx512.readQuad ha').v14
    ∧ R43x6.U44 (Avx512.readQuad ha').v25) →

  let avxResult := StateT.run (runFunction (Avx512.fd_ed25519_point_dbln.denote
    (Ctxt.Valuation.ofHVector [.value n, .value a', .value r']ₕ))) s'

  let P := Ref.readPoint ha
  let P' := (Avx512.readQuad ha').toPoint
  P.X = P'.X → P.Y = P'.Y → P.Z = P'.Z →

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
      ∧ Ref.readPoint hrOut = P.dbln n

end Firedancer

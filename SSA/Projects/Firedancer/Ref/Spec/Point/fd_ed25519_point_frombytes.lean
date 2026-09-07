/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_frombytes
import SSA.Projects.Firedancer.Ref.Spec.Point
import SSA.Projects.Firedancer.Curve

import SSA.Projects.Firedancer.Prime
import Mathlib.Algebra.Group.Even

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- Point decompression, RFC 8032 §5.1.3: `buf` is `y` with the sign of `x` in
its top bit, and `r` becomes the point it names -- or the call writes nothing
and returns `NULL`.

`y = decodeBytes buf` masks bit 255 and reduces, so a non-canonical encoding
decodes rather than being rejected. The encoding names a point exactly when
`(y²-1)/(d y²+1)` is a square -- `fd_f25519_sqrt_ratio`'s flag -- and then `r`
holds `(x : y : 1 : x·y)`, with `x` the root whose sign is the masked bit.

`d` and `1` reach the region through `llvm.mlir.addressof`, so they are
constants of the field here, and a conformance proof supplies `HoldsGlobal`
for `@fd_f25519_d` and `@fd_f25519_one`.
-/
abbrev fd_ed25519_point_frombytes_spec (r buf : Pointer) (s : GlobalState)
    (hr : IsPointPtr s.mem r) (hbuf : IsByteBufPtr s.mem buf) : Prop :=
  let invocation := runFunction (fd_ed25519_point_frombytes.denote
    (Ctxt.Valuation.ofHVector [.value buf, .value r]ₕ))
  let result := StateT.run invocation s
  let bytes := readBuf hbuf
  let y : ZMod p := decodeBytes bytes
  let sign := bytes.getLsbD 255
  let isSquare := IsSquare ((y^2 - 1) / (d * y^2 + 1))

  ∃ (s' : GlobalState) (ret : PoisonOr Pointer),
    result = .value ([ret]ₕ, s') ∧
    ∃ (oX oY oZ oT : Fin 5 → BitVec 64),
      (¬ isSquare → ret = SLLVM.Ptr.null ∧ s ≈ s') ∧
      (isSquare → ret = .value r ∧
        let outMem := (((s.mem.splice r (packLimbs oX)).splice (r.withOffset 40) (packLimbs oY)).splice
          (r.withOffset 120) (packLimbs oZ)).splice (r.withOffset 80) (packLimbs oT)
        let output_state : GlobalState := { s with mem := outMem }
        s' ≈ output_state ∧
        have output_state_pointPtr := isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hr (q₁ := r) (x := packLimbs oX)) (q₁ := r.withOffset 40) (x := packLimbs oY)) (q₁ := r.withOffset 120) (x := packLimbs oZ)) (q₁ := r.withOffset 80) (x := packLimbs oT)
        let readPoint := readPoint output_state_pointPtr
        OnCurve readPoint.x readPoint.y ∧
        readPoint.Z = 1 ∧
        readPoint.Y = y ∧
        readPoint.T / readPoint.Z = readPoint.x * readPoint.y ∧
        (readPoint.X ≠ 0 → ((readPoint.X.val % 2 == 0) ↔ (sign = false)))
      )

end Firedancer.Ref

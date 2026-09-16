/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_frombytes
import SSA.Projects.Firedancer.Ref.Spec.Point
import SSA.Projects.Firedancer.Ref.Spec.Bias
import SSA.Projects.Firedancer.Ref.Spec.Field.fd_f25519_is_zero
import SSA.Projects.Firedancer.Curve

import SSA.Projects.Firedancer.Prime
import Mathlib.Algebra.Group.Even

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- The four coordinate writes a successful decompression leaves at `r`, in
the order `fd_ed25519_point_from` stores them (`X, Y, Z, T` at 0, 40, 120,
80).

A `def`, not an `abbrev`: reducible, every unifier that meets it walks four
splices of `packLimbs`, and the proofs pay for it at each `live?`. It unfolds
where a proof asks (`simp only [pointOutMem]`), and `live?_pointOutMem_ne`
covers what the walks actually need. -/
def pointOutMem (m : MemoryState) (r : Pointer) (oX oY oZ oT : Fin 5 → BitVec 64) : MemoryState :=
  (((m.splice r (packLimbs oX)).splice (r.withOffset 40) (packLimbs oY)).splice (r.withOffset 120)
        (packLimbs oZ)).splice
    (r.withOffset 80) (packLimbs oT)

/-- The four stores leave a point where one was. Named, so that a proof
transporting a decoding between memories rewrites `readPoint` at a term it
shares with the spec. -/
theorem isPointPtr_pointOutMem {m : MemoryState} {r : Pointer} (hr : IsPointPtr m r)
    (oX oY oZ oT : Fin 5 → BitVec 64) : IsPointPtr (pointOutMem m r oX oY oZ oT) r := by
  simp only [pointOutMem]
  exact isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hr)))

/-- What a decompressed point satisfies: `(x : y : 1 : x·y)` for the `y` the
buffer encodes, `x` the root whose sign is the buffer's top bit. The sign
clause is guarded -- at `x = 0` the region accepts either bit, where RFC 8032
and Dalek reject the set one.

Stated over the point and the bytes rather than over memory, so that a caller
transporting it between two memories rewrites two arguments instead of
reaching under a binder. -/
abbrev IsDecoding (point : Point) (bytes : BitVec 256) : Prop :=
  OnCurve point.x point.y ∧
    point.Z = 1 ∧
    point.Y = decodeBytes bytes ∧
    point.T / point.Z = point.x * point.y ∧
    (point.X ≠ 0 → (point.X.val % 2 = 0 ↔ bytes[255] = false))

/-- ... as read out of the memory the four stores left. -/
abbrev DecodesTo (m : MemoryState) (r buf : Pointer) (hr : IsPointPtr m r)
    (hbuf : IsByteBufPtr m buf) (oX oY oZ oT : Fin 5 → BitVec 64) : Prop :=
  IsDecoding (readPoint (isPointPtr_pointOutMem hr oX oY oZ oT)) (readBuf hbuf)

/-- The limbs a decompression leaves at `r`: `X` at `fd_f25519_neg`'s bias bound, since the
region negates without carrying, and `Y`, `T`, `Z` tight; and a zero `X` in one of the two
patterns `fd_f25519_is_zero` accepts. In `DecodesTo`'s shape, so a `simp` over the stores
leaves it alone. -/
abbrev DecodedBounds (m : MemoryState) (r : Pointer) (hr : IsPointPtr m r)
    (oX oY oZ oT : Fin 5 → BitVec 64) : Prop :=
  let h := isPointPtr_pointOutMem hr oX oY oZ oT
  BiasBounds (isCoordPtr h 0) ∧
    LimbBounds (isCoordPtr h 1) ∧
    LimbBounds (isCoordPtr h 2) ∧
    LimbBounds (isCoordPtr h 3) ∧ ZeroRep r (pointOutMem m r oX oY oZ oT)

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
abbrev fd_ed25519_point_frombytes_spec (r buf : Pointer) (s : GlobalState) (hr : IsPointPtr s.mem r)
    (hbuf : IsByteBufPtr s.mem buf) : Prop :=
  let invocation :=
    runFunction
      (fd_ed25519_point_frombytes.denote (Ctxt.Valuation.ofHVector [.value buf, .value r]ₕ))
  let result := StateT.run invocation s
  let isSquare :=
    IsSquare ((decodeBytes (readBuf hbuf) ^ 2 - 1) / (d * decodeBytes (readBuf hbuf) ^ 2 + 1))
  ∃ (s' : GlobalState) (ret : PoisonOr Pointer),
    result = .value ([ret]ₕ, s') ∧
      ∃ oX oY oZ oT : Fin 5 → BitVec 64,
        (¬isSquare → ret = SLLVM.Ptr.null ∧ s ≈ s') ∧
          (isSquare →
            ret = .value r ∧
              s' ≈ ({ s with mem := pointOutMem s.mem r oX oY oZ oT } : GlobalState) ∧
              DecodesTo s.mem r buf hr hbuf oX oY oZ oT ∧ DecodedBounds s.mem r hr oX oY oZ oT)

end Firedancer.Ref

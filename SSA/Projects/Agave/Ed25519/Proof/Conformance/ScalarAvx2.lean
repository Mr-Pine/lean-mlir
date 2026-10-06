import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.Algebra
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ControlFlow
import SSA.Projects.Agave.Ed25519.Bridge.Encoding

/-!
# Unconditional scalar/AVX2 equality at the pure verifier boundary

The backend functions here are the concrete `serialMath` and `avx2Math`, with
their proved NAF construction, point formulas, and actual basepoint tables.
Their equality is proved, not supplied as a backend-correctness hypothesis.
The common operations (including decoding, scalar parsing, and the challenge)
may be arbitrary: replacing just the backend preserves every Boolean result.

These are pure verifier theorems. They do not identify the helper parameters
with their extracted implementations or claim whole-verifier RIR conformance.
In particular, the canonical encoder below is the mathematical encoding, not
an execution theorem for the pointer-based point compressor.
-/

namespace Agave.Ed25519.Conformance

open PointArithmetic Tables Verifier DoubleBase

/-- The common canonical Edwards byte encoding, including canonical x parity. -/
def encodeAffine (xy : F × F) : Bytes32 :=
  BitVec.ofNat 1 (xy.1.val % 2) ++ BitVec.ofNat 255 xy.2.val

theorem encodeAffine_eq_curve_compress (P : Bridge.CurvePoint) :
    encodeAffine (P.x, P.y) = Bridge.compress P := rfl

def compressMath (P : Extended F) : Bytes32 := compressWith encodeAffine P

/-- Backend equality needs no curve, scalar-bound, or encoding-validity premise.
It follows from the concrete formula/table correspondence already proved. -/
theorem scalar_avx2_math_compression_eq (h s : Nat) (A : Extended F) :
    compressMath (serialMath h A s) = compressMath (avx2Math h A s) :=
  (double_base_math_compress_eq encodeAffine h s A).symm

/-- All byte strings, including malformed A/R/S, give the same pure verification
result. `coordinates` allows the shared decoder to use any common point type. -/
theorem pure_scalar_avx2_all_inputs {Point : Type}
    (shared : Shared Point Nat) (coordinates : Point → Extended F)
    (a r s : Bytes32) (h : Nat) :
    verify shared (fun h A s => serialMath h (coordinates A) s) compressMath a r s h =
      verify shared (fun h A s => avx2Math h (coordinates A) s) compressMath a r s h := by
  apply verify_congr
  intro A R scalar _ _ _ _ _
  exact scalar_avx2_math_compression_eq h scalar (coordinates (shared.negate A))

/-- Complete message inputs require only that the two sides use the same
challenge function; neither SHA correctness nor a challenge bound is needed
for this backend-replacement theorem. -/
theorem pure_scalar_avx2_all_messages {Point : Type}
    (shared : Shared Point Nat) (coordinates : Point → Extended F)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Nat)
    (a r s : Bytes32) (message : List (BitVec 8)) :
    verify shared (fun h A s => serialMath h (coordinates A) s) compressMath
        a r s (challenge r a message) =
      verify shared (fun h A s => avx2Math h (coordinates A) s) compressMath
        a r s (challenge r a message) :=
  pure_scalar_avx2_all_inputs shared coordinates a r s (challenge r a message)

end Agave.Ed25519.Conformance

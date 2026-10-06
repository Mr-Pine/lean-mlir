import Mathlib

/-!
# Strict Ed25519 verification control flow

This is the pure control-flow layer for `solana-ed25519` 0.2.4,
`ed_sigs/verification_key.rs:205-218,391-427`. Public-key construction first
decompresses A and stores -A. `verify_dalek_prehashed` rejects small-order -A,
decompresses R, rejects small-order R, parses canonical S, then compares the
compressed double-scalar result with the original R bytes.

The functions below are explicit parameters, not axioms or claimed execution
refinements. An RIR conformance theorem must connect its calls to these
parameters. In particular, the backend premise below still needs the complete
double-scalar proof; this module does not discharge it by assumption silently.
-/

namespace Agave.Ed25519.Verifier

abbrev Bytes32 := BitVec 256

/-- Shared operations outside the runtime-selected double-scalar backend. -/
structure Shared (Point Scalar : Type) where
  decompress : Bytes32 → Option Point
  negate : Point → Point
  smallOrder : Point → Bool
  parseScalar : Bytes32 → Option Scalar

/-- The checks on an already constructed `VerificationKey`, in source order.
`minusA` is the cached negation, not the encoded public key. -/
def prehashed {Point Scalar Result : Type} (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result)
    (compress : Result → Bytes32) (minusA : Point) (r s : Bytes32)
    (challenge : Scalar) : Bool :=
  if shared.smallOrder minusA then false else
  match shared.decompress r with
  | none => false
  | some R =>
    if shared.smallOrder R then false else
    match shared.parseScalar s with
    | none => false
    | some scalar => decide (compress (doubleBase challenge minusA scalar) = r)

/-- Byte-input verification, including public-key construction. -/
def verify {Point Scalar Result : Type} (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result)
    (compress : Result → Bytes32) (a r s : Bytes32) (challenge : Scalar) : Bool :=
  match shared.decompress a with
  | none => false
  | some A => prehashed shared doubleBase compress (shared.negate A) r s challenge

/-- Exact acceptance condition; failures in every preceding check return false.
No correctness hypotheses on the parameter functions are needed. -/
theorem prehashed_eq_true_iff {Point Scalar Result : Type}
    (shared : Shared Point Scalar) (doubleBase : Scalar → Point → Scalar → Result)
    (compress : Result → Bytes32) (minusA : Point) (r s : Bytes32) (h : Scalar) :
    prehashed shared doubleBase compress minusA r s h = true ↔
      shared.smallOrder minusA = false ∧ ∃ R scalar,
        shared.decompress r = some R ∧ shared.smallOrder R = false ∧
        shared.parseScalar s = some scalar ∧ compress (doubleBase h minusA scalar) = r := by
  cases hA : shared.smallOrder minusA <;> simp [prehashed, hA]
  cases hR : shared.decompress r with
  | none => simp
  | some R =>
    cases hsmall : shared.smallOrder R <;> simp [hsmall]
    cases hs : shared.parseScalar s <;> simp

theorem verify_eq_true_iff {Point Scalar Result : Type}
    (shared : Shared Point Scalar) (doubleBase : Scalar → Point → Scalar → Result)
    (compress : Result → Bytes32) (a r s : Bytes32) (h : Scalar) :
    verify shared doubleBase compress a r s h = true ↔
      ∃ A R scalar, shared.decompress a = some A ∧
        shared.smallOrder (shared.negate A) = false ∧
        shared.decompress r = some R ∧ shared.smallOrder R = false ∧
        shared.parseScalar s = some scalar ∧
        compress (doubleBase h (shared.negate A) scalar) = r := by
  cases ha : shared.decompress a <;>
    simp [verify, ha, prehashed_eq_true_iff]

/-- Backend replacement only needs equal compressed observations on successful
paths; there is no requirement on backend calls that verification never makes. -/
theorem verify_congr {Point Scalar Left Right : Type}
    (shared : Shared Point Scalar)
    (left : Scalar → Point → Scalar → Left) (right : Scalar → Point → Scalar → Right)
    (compressLeft : Left → Bytes32) (compressRight : Right → Bytes32)
    (a r s : Bytes32) (h : Scalar)
    (heq : ∀ A R scalar, shared.decompress a = some A →
      shared.smallOrder (shared.negate A) = false →
      shared.decompress r = some R → shared.smallOrder R = false →
      shared.parseScalar s = some scalar →
      compressLeft (left h (shared.negate A) scalar) =
        compressRight (right h (shared.negate A) scalar)) :
    verify shared left compressLeft a r s h = verify shared right compressRight a r s h := by
  apply Bool.eq_iff_iff.mpr
  simp only [verify_eq_true_iff]
  constructor
  · rintro ⟨A, R, scalar, ha, hA, hr, hR, hs, hout⟩
    exact ⟨A, R, scalar, ha, hA, hr, hR, hs, (heq A R scalar ha hA hr hR hs) ▸ hout⟩
  · rintro ⟨A, R, scalar, ha, hA, hr, hR, hs, hout⟩
    exact ⟨A, R, scalar, ha, hA, hr, hR, hs, (heq A R scalar ha hA hr hR hs).symm ▸ hout⟩

/-- Equal affine points suffice even when the backend result types and internal
limbs differ. Compression must factor through the same affine encoding. -/
theorem verify_eq_of_affine_eq {Point Scalar Left Right Affine : Type}
    (shared : Shared Point Scalar)
    (left : Scalar → Point → Scalar → Left) (right : Scalar → Point → Scalar → Right)
    (affineLeft : Left → Affine) (affineRight : Right → Affine)
    (encode : Affine → Bytes32)
    (compressLeft : Left → Bytes32) (compressRight : Right → Bytes32)
    (hcLeft : ∀ x, compressLeft x = encode (affineLeft x))
    (hcRight : ∀ x, compressRight x = encode (affineRight x))
    (heq : ∀ h A s, affineLeft (left h A s) = affineRight (right h A s))
    (a r s : Bytes32) (h : Scalar) :
    verify shared left compressLeft a r s h = verify shared right compressRight a r s h := by
  apply verify_congr
  intro A R scalar _ _ _ _ _
  rw [hcLeft, hcRight, heq]

/-- The same result for arbitrary message bytes, using a shared challenge
function. This theorem does not assert correctness of SHA-512 or its reduction. -/
theorem verify_message_congr {Point Scalar Left Right : Type}
    (shared : Shared Point Scalar)
    (left : Scalar → Point → Scalar → Left) (right : Scalar → Point → Scalar → Right)
    (compressLeft : Left → Bytes32) (compressRight : Right → Bytes32)
    (heq : ∀ h A s, compressLeft (left h A s) = compressRight (right h A s))
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (a r s : Bytes32) (msg : List (BitVec 8)) :
    verify shared left compressLeft a r s (challenge r a msg) =
      verify shared right compressRight a r s (challenge r a msg) := by
  apply verify_congr
  intro A R scalar _ _ _ _ _
  exact heq _ _ _

end Agave.Ed25519.Verifier

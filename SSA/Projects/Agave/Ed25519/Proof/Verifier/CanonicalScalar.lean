import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekScalarCanonical
import SSA.Projects.Agave.Ed25519.Proof.Verifier.AcceptanceRepresented

/-! Bounded scalars avoid the modulo-`2^256` representation aliases of `Nat`. -/

namespace Agave.Ed25519.Verifier
open Bridge

abbrev CanonicalScalar := Fin subgroupOrder

namespace CanonicalScalar

def encode (s : CanonicalScalar) : Bytes32 := BitVec.ofNat 256 s.val

def parse (s : Bytes32) : Option CanonicalScalar :=
  if h : s.toNat < subgroupOrder then some ⟨s.toNat, h⟩ else none

theorem bound (s : CanonicalScalar) : s.val < 2 ^ 255 :=
  lt_trans s.isLt subgroupOrder_lt_two_pow_255

theorem encode_toNat (s : CanonicalScalar) : (encode s).toNat = s.val := by
  have hb := bound s
  exact Nat.mod_eq_of_lt (by omega)

theorem encode_eq_iff (s : CanonicalScalar) (bytes : Bytes32) :
    encode s = bytes ↔ s.val = bytes.toNat := by
  constructor
  · intro h
    simpa only [encode_toNat] using congrArg BitVec.toNat h
  · intro h
    apply BitVec.eq_of_toNat_eq
    exact (encode_toNat s).trans h

theorem parse_eq_some_iff (bytes : Bytes32) (s : CanonicalScalar) :
    parse bytes = some s ↔ s.val = bytes.toNat ∧ bytes.toNat < subgroupOrder := by
  by_cases h : bytes.toNat < subgroupOrder
  · simp [parse, h, Fin.ext_iff, eq_comm]
  · simp [parse, h]

theorem complete (n : Nat) (h : n < subgroupOrder) :
    ∃ s : CanonicalScalar, s.val = n := ⟨⟨n, h⟩, rfl⟩

def layout (original : Execution.Dalek.Layout Point CanonicalScalar Result) :
    Execution.Dalek.Layout Point CanonicalScalar Result :=
  { original with scalar := encode, reduce := Execution.Dalek.reduceScalarBytes }

def shared (original : Shared Point CanonicalScalar) : Shared Point CanonicalScalar :=
  { original with parseScalar := parse }

theorem parserContracts (original : Execution.Dalek.Layout Point CanonicalScalar Result)
    (operations : Shared Point CanonicalScalar) :
    Execution.Dalek.ScalarParseContract (layout original) (shared operations) ∧
    Execution.Dalek.ScalarParseComplete (layout original) (shared operations) := by
  have hgate (bytes : Bytes32) :
      Execution.Dalek.scalarGate (layout original) bytes = true ↔
        bytes.toNat < subgroupOrder :=
    Execution.Dalek.scalarGate_iff_canonical (layout original) (fun _ => rfl) bytes
  constructor
  · intro bytes s
    change parse bytes = some s ↔
      Execution.Dalek.scalarGate (layout original) bytes = true ∧ encode s = bytes
    rw [parse_eq_some_iff, hgate, encode_eq_iff, and_comm]
  · intro bytes hg
    have hb := (hgate bytes).mp hg
    refine ⟨⟨bytes.toNat, hb⟩, ?_⟩
    change parse bytes = some ⟨bytes.toNat, hb⟩
    exact (parse_eq_some_iff _ _).mpr ⟨rfl, hb⟩

/-- The bounded parser discharges the scalar fields of the represented
acceptance interface. Only the point semantics remain premises. -/
theorem representedSharedCorrect (operations : Shared Point CanonicalScalar)
    (toCurve : Point → CurvePoint)
    (hdecompress : ∀ bytes P, operations.decompress bytes = some P →
      Encodes bytes (toCurve P))
    (hcomplete : ∀ bytes P, Encodes bytes P →
      ∃ p, operations.decompress bytes = some p ∧ toCurve p = P)
    (hnegate : ∀ P, toCurve (operations.negate P) = -toCurve P)
    (hsmall : ∀ P, operations.smallOrder P = false ↔ (8 : Nat) • toCurve P ≠ 0) :
    RepresentedSharedCorrect (shared operations) toCurve Fin.val :=
  ⟨hdecompress, hcomplete, hnegate, hsmall, parse_eq_some_iff, complete⟩

end CanonicalScalar

/-- Formal obstruction in the intended older endpoint: an unbounded natural
scalar encoded by truncation cannot satisfy Dalek's parser contract even at
the single accepted scalar zero. -/
theorem not_nat_ofNat_scalarParseContract
    (layout : Execution.Dalek.Layout Point Nat Result) (operations : Shared Point Nat)
    (hencode : ∀ n, layout.scalar n = BitVec.ofNat 256 n)
    (hzero : operations.parseScalar 0 = some 0) :
    ¬ Execution.Dalek.ScalarParseContract layout operations := by
  intro hcontract
  have h := Execution.Dalek.scalarParseContract_no_alias layout operations hcontract
    0 0 (2 ^ 256) hzero (by rw [hencode, hencode]; decide)
  have hpositive : 0 < (2 : Nat) ^ 256 := by decide
  omega

end Agave.Ed25519.Verifier

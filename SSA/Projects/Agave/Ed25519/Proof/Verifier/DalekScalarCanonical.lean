import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionContracts
import SSA.Projects.Agave.Ed25519.UpstreamMath.Canonicality

/-!
# Canonical scalar adapters for the exact Dalek gate

The gate uses the actual signed-byte comparison and byte-for-byte reduction
equality from the imported caller. These adapters discharge the mathematical
parser obligations once the scalar reduction's byte result is established.
They do not supply an execution theorem for the scalar reduction callee.
`Reduce64` reduces AVX2 base-field limbs, not scalars modulo the subgroup order,
and therefore cannot discharge that remaining callee obligation.

The byte-valued parser is total, including noncanonical input. The scalar
representation is the original 32 bytes; interpreting successful results as
natural numbers is justified by `parseCanonicalBytes_eq_some_iff`.
-/

namespace Agave.Ed25519.Verifier.Execution.Dalek

open Agave.Ed25519.UpstreamMath.Canonicality

/-- Mathematical scalar reduction, with the same 32-byte result width as the
actual scalar reduction callee. -/
def reduceScalarBytes (s : Bytes32) : Bytes32 :=
  BitVec.ofNat 256 (s.toNat % ell)

/-- All byte strings have a defined parser result, including rejected ones. -/
def parseCanonicalBytes (s : Bytes32) : Option Bytes32 :=
  if s.toNat < ell then some s else none

theorem reduceScalarBytes_toNat (s : Bytes32) :
    (reduceScalarBytes s).toNat = s.toNat % ell := by
  have hm := Nat.mod_lt s.toNat ell_pos
  have he := ell_lt_253
  have hb : s.toNat % ell < 2 ^ 256 := by omega
  simp only [reduceScalarBytes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]

theorem reduceScalarBytes_eq_self_iff (s : Bytes32) :
    reduceScalarBytes s = s ↔ s.toNat < ell := by
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    rw [reduceScalarBytes_toNat] at hn
    have hm := Nat.mod_lt s.toNat ell_pos
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [reduceScalarBytes_toNat, Nat.mod_eq_of_lt h]

/-- Canonicality makes the exact signed comparison of the last byte succeed.
This is a proof about the RIR caller's expression, not a substituted guard. -/
theorem scalarHighBitClear_of_canonical (s : Bytes32) (h : s.toNat < ell) :
    scalarHighBitClear s = true := by
  have hb : s.toNat < 2 ^ 255 := ((scalarParserTest_iff s.toNat).mpr h).1
  have hbyte : (s.extractLsb' 248 8).toNat < 128 := by
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    omega
  have hint : (s.extractLsb' 248 8).toInt =
      ((s.extractLsb' 248 8).toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by omega)
  unfold scalarHighBitClear
  rw [BitVec.slt_eq_decide, decide_eq_true_eq, hint]
  have hminus : (-1 : BitVec 8).toInt = -1 := by decide
  rw [hminus]
  omega

/-- The only remaining premise here is the mathematical result of reduction;
the high-bit test and rejection completeness are proved. -/
theorem scalarGate_iff_canonical
    (layout : Layout Point Scalar Result)
    (hreduce : ∀ s, layout.reduce s = reduceScalarBytes s) (s : Bytes32) :
    scalarGate layout s = true ↔ s.toNat < ell := by
  simp only [scalarGate, Bool.and_eq_true, decide_eq_true_eq, hreduce,
    reduceScalarBytes_eq_self_iff]
  exact ⟨fun h => h.2, fun h => ⟨scalarHighBitClear_of_canonical s h, h⟩⟩

theorem parseCanonicalBytes_eq_some_iff (s scalar : Bytes32) :
    parseCanonicalBytes s = some scalar ↔ s.toNat < ell ∧ scalar = s := by
  by_cases h : s.toNat < ell
  · simp [parseCanonicalBytes, h, eq_comm]
  · simp [parseCanonicalBytes, h]

/-- Instantiate arbitrary point/backend layouts with a byte-valued canonical
scalar representation. No claims about point operations are needed. -/
theorem scalarParseContract_of_canonicalBytes
    (layout : Layout Point Bytes32 Result) (shared : Shared Point Bytes32)
    (hscalar : ∀ s, layout.scalar s = s)
    (hreduce : ∀ s, layout.reduce s = reduceScalarBytes s)
    (hparse : ∀ s, shared.parseScalar s = parseCanonicalBytes s) :
    ScalarParseContract layout shared := by
  intro s scalar
  rw [hparse, parseCanonicalBytes_eq_some_iff,
    scalarGate_iff_canonical layout hreduce, hscalar]

theorem scalarParseComplete_of_canonicalBytes
    (layout : Layout Point Bytes32 Result) (shared : Shared Point Bytes32)
    (hreduce : ∀ s, layout.reduce s = reduceScalarBytes s)
    (hparse : ∀ s, shared.parseScalar s = parseCanonicalBytes s) :
    ScalarParseComplete layout shared := by
  intro s hgate
  refine ⟨s, ?_⟩
  rw [hparse, parseCanonicalBytes_eq_some_iff]
  exact ⟨(scalarGate_iff_canonical layout hreduce s).mp hgate, rfl⟩

/-- A bundled specialization discharges both parser leaves, including inputs
rejected by the canonical parser. -/
theorem scalarParserContracts_of_canonicalBytes
    (layout : Layout Point Bytes32 Result) (shared : Shared Point Bytes32)
    (hscalar : ∀ s, layout.scalar s = s)
    (hreduce : ∀ s, layout.reduce s = reduceScalarBytes s)
    (hparse : ∀ s, shared.parseScalar s = parseCanonicalBytes s) :
    ScalarParseContract layout shared ∧ ScalarParseComplete layout shared :=
  ⟨scalarParseContract_of_canonicalBytes layout shared hscalar hreduce hparse,
    scalarParseComplete_of_canonicalBytes layout shared hreduce hparse⟩

/-- Install the proved scalar representation while retaining the point and
backend representation choices of the caller. -/
def withCanonicalScalarLayout (layout : Layout Point Bytes32 Result) :
    Layout Point Bytes32 Result :=
  { layout with scalar := id, reduce := reduceScalarBytes }

def withCanonicalScalarParser (shared : Shared Point Bytes32) : Shared Point Bytes32 :=
  { shared with parseScalar := parseCanonicalBytes }

/-- Both scalar parser leaves are closed for this concrete pure instantiation.
The scalar reduction execution contract remains a separate machine obligation. -/
theorem canonicalScalarParserContracts
    (layout : Layout Point Bytes32 Result) (shared : Shared Point Bytes32) :
    ScalarParseContract (withCanonicalScalarLayout layout)
      (withCanonicalScalarParser shared) ∧
    ScalarParseComplete (withCanonicalScalarLayout layout)
      (withCanonicalScalarParser shared) :=
  scalarParserContracts_of_canonicalBytes _ _ (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl)

/-- The parser contract requires unambiguous scalar representations at every
accepted byte string. In particular an unrestricted `Nat` represented by
`BitVec.ofNat 256` cannot satisfy it: adding `2^256` aliases the representation.
Byte-valued or bounded scalar types avoid that obstruction. -/
theorem scalarParseContract_no_alias
    (layout : Layout Point Scalar Result) (shared : Shared Point Scalar)
    (hparse : ScalarParseContract layout shared)
    (s : Bytes32) (a b : Scalar) (ha : shared.parseScalar s = some a)
    (hab : layout.scalar a = layout.scalar b) : a = b := by
  obtain ⟨hgate, hbytes⟩ := (hparse s a).mp ha
  have hb := (hparse s b).mpr ⟨hgate, hab.symm.trans hbytes⟩
  exact Option.some.inj (ha.symm.trans hb)

end Agave.Ed25519.Verifier.Execution.Dalek

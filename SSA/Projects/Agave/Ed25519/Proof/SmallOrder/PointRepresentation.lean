import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Contract
import SSA.Projects.Agave.Ed25519.Proof.Verifier.KeyPayloadLayout
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityArithmetic
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.WordRefinement

/-! Reuse the constructor's exact noncanonical coordinate payload. Tightness
is explicit and distinct from homogeneous curve representation; neither one
follows merely from possessing 160 readable bytes. -/
namespace Agave.Ed25519.SmallOrder
open LeanMLIR.RIR
open Verifier.Execution
open SerialPoint

abbrev ConcretePoint := Key.PointWords

def words (P : ConcretePoint) : WordPoint := ⟨P.X, P.Y, P.Z, P.T⟩

def coordinates (P : ConcretePoint) (c : Fin 4) : Field.Serial :=
  ![P.X, P.Y, P.Z, P.T] c

def TightRepresentation (P : ConcretePoint) (A : Bridge.CurvePoint) : Prop :=
  PointTight (unsignedPoint (words P)) ∧ P.Represents A

private theorem pack_pair_zero (a b : BitVec 64) :
    (BitVec.packLanes #v[a, b]).extractLsb' 0 64 = a := by
  simpa using BitVec.extractLsb'_packLanes #v[a, b] 0 (by decide)

private theorem pack_pair_one (a b : BitVec 64) :
    (BitVec.packLanes #v[a, b]).extractLsb' 64 64 = b := by
  simpa using BitVec.extractLsb'_packLanes #v[a, b] 1 (by decide)

/-- Exact limb readback from the existing constructor payload, not a new
canonical representation chosen for this proof. -/
theorem payload_word (P : ConcretePoint) (c : Fin 4) (i : Fin 5) :
    P.bytes.extractLsb' (320*c.val + 64*i.val) 64 = coordinates P c i := by
  fin_cases c <;> fin_cases i <;>
    simp (disch := decide) [Key.PointWords.bytes, Key.pointPayload,
      Key.coordinatePayload, coordinates,
      Memory.extractLsb'_spliceBits_of_disjoint,
      Memory.extractLsb'_spliceBits_of_subrange,
      Memory.extractLsb'_spliceBits_self, pack_pair_zero, pack_pair_one]

/-- A caller-visible full payload observation supplies the five raw words
actually read at each field multiplication's coordinate argument. -/
theorem read_coordinate (s : GlobalState) (p : Pointer) (P : ConcretePoint)
    (h : Dalek.ReadBytes s p 160 P.bytes) (c : Fin 4) :
    SerialFieldMul.readLimbs s (p.add (BitVec.ofNat 64 (40*c.val))) = coordinates P c := by
  funext i
  have hk : 40*c.val + 8*i.val < 2^64 := by omega
  have hbits : (BitVec.ofNat 64 (40*c.val + 8*i.val)).toNat * 8 + 64 ≤ 1280 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
    omega
  have he := MemoryState.readAt_add_of_readAt h.1.fits
    (h.1.no_wrap (k := 40*c.val + 8*i.val) (by omega)) hbits h.2
  have hoff : (40*c.val + 8*i.val)*8 = 320*c.val + 64*i.val := by omega
  have he' : s.mem.readAt (p.add (BitVec.ofNat 64 (40*c.val + 8*i.val))) 64 =
      P.bytes.extractLsb' (320*c.val + 64*i.val) 64 := by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, hoff] using he
  simpa only [SerialFieldMul.readLimbs, Pointer.add_add, ← BitVec.ofNat_add] using
    he'.trans (payload_word P c i)

/-- Uniform multiplication input bounds come from the point invariant. -/
theorem coordinate_bounded (P : ConcretePoint) (h : PointTight (unsignedPoint (words P)))
    (c : Fin 4) : SerialFieldMul.Bounded (SerialFieldMul.unsigned (coordinates P c)) := by
  have hb := pointTight_bounded _ h
  fin_cases c
  · exact hb.1
  · exact hb.2.1
  · exact hb.2.2.1
  · exact hb.2.2.2

end Agave.Ed25519.SmallOrder

import SSA.Projects.Agave.Ed25519.Proof.Encoding.ToBytesCorrectness
import SSA.Projects.Agave.Ed25519.Spec.PointArithmetic
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionContracts
import Mathlib.Data.ZMod.Basic

/-! Canonical serialization compares field values, not limb representatives.
The exact equality body multiplies X1*Z2, X2*Z1, Y1*Z2, Y2*Z1 before these
comparisons. Executing its four inlined serializers remains a separate task. -/
namespace Agave.Ed25519.SmallOrder
open Encoding PointArithmetic
open Verifier.Execution.Dalek

abbrev K := ZMod Encoding.modulus

/-- Existing unrestricted-u64 serialization correctness closes the value
comparison for arbitrary limb representatives, including noncanonical ones. -/
theorem machineBytes_eq_iff (a b : Field.Serial) :
    machineBytes a = machineBytes b ↔
      (Field.serialValue a : K) = (Field.serialValue b : K) := by
  rw [ZMod.natCast_eq_natCast_iff']
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    simpa only [machineBytes_canonical] using hn
  · intro h
    apply BitVec.eq_of_toNat_eq
    simpa only [machineBytes_canonical] using h

def crossEqual (P Q : Extended K) : Prop :=
  P.X * Q.Z = Q.X * P.Z ∧ P.Y * Q.Z = Q.Y * P.Z

/-- The actual identity has X=0 and Y=Z=1. No division or nonzero-Z
assumption is smuggled into the point-equality arithmetic. -/
theorem crossEqual_identity (P : Extended K) :
    crossEqual P ⟨0, 1, 1, 0⟩ ↔ P.X = 0 ∧ P.Y = P.Z := by
  simp [crossEqual]

/-- Four multiplication value equations suffice for the two canonical byte
comparisons to be exactly the projective-coordinate comparison. -/
theorem serialized_crossEqual (P Q : Extended K) (xz zx yz zy : Field.Serial)
    (hxz : (Field.serialValue xz : K) = P.X * Q.Z)
    (hzx : (Field.serialValue zx : K) = Q.X * P.Z)
    (hyz : (Field.serialValue yz : K) = P.Y * Q.Z)
    (hzy : (Field.serialValue zy : K) = Q.Y * P.Z) :
    (machineBytes xz = machineBytes zx ∧ machineBytes yz = machineBytes zy) ↔
      crossEqual P Q := by
  rw [machineBytes_eq_iff, machineBytes_eq_iff, hxz, hzx, hyz, hzy]
  rfl

/-- Exact 0/1 Choice ABI for the AND executed after the two byte comparisons. -/
theorem choice_conjunction (x y : Bool) :
    choiceByte y &&& choiceByte x = choiceByte (x && y) := by
  cases x <;> cases y <;> decide

end Agave.Ed25519.SmallOrder

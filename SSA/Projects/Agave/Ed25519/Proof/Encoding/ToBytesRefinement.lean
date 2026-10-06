import SSA.Projects.Agave.Ed25519.Proof.Encoding.ToBytesCorrectness
import SSA.Projects.Agave.Ed25519.Proof.Encoding.ToBytesExecution
import SSA.Projects.Agave.Ed25519.Proof.Encoding.PointBytes

namespace Agave.Ed25519.Encoding
open LeanMLIR.RIR
open _root_.Ed25519 Bridge

/-! Each theorem below joins exact RIR execution to the canonical limb
packing. Inputs are unrestricted u64 limbs. The state well-formedness premise
is the RIR execution invariant; no arithmetic flag or canonicality premise
is left to the caller. -/

theorem to_bytes0_canonical_call (a : Field.Serial) (s : GlobalState) (hwf : s.WF) :
    RIR.agave_serial_field_to_bytes_observe_0.call
      (RIR.agave_serial_field_to_bytes_observe_0.args
        (.value (a 0)) (.value (a 1)) (.value (a 2)) (.value (a 3)) (.value (a 4))) s =
      .value (.cons (.value (packWords (tightWords a) 0)) .nil, s) := by
  rw [RIR.to_bytes0_call _ _ _ _ _ s hwf, machine0_pack]

theorem to_bytes1_canonical_call (a : Field.Serial) (s : GlobalState) (hwf : s.WF) :
    RIR.agave_serial_field_to_bytes_observe_1.call
      (RIR.agave_serial_field_to_bytes_observe_1.args
        (.value (a 0)) (.value (a 1)) (.value (a 2)) (.value (a 3)) (.value (a 4))) s =
      .value (.cons (.value (packWords (tightWords a) 1)) .nil, s) := by
  rw [RIR.to_bytes1_call _ _ _ _ _ s hwf, machine1_pack]

theorem to_bytes2_canonical_call (a : Field.Serial) (s : GlobalState) (hwf : s.WF) :
    RIR.agave_serial_field_to_bytes_observe_2.call
      (RIR.agave_serial_field_to_bytes_observe_2.args
        (.value (a 0)) (.value (a 1)) (.value (a 2)) (.value (a 3)) (.value (a 4))) s =
      .value (.cons (.value (packWords (tightWords a) 2)) .nil, s) := by
  rw [RIR.to_bytes2_call _ _ _ _ _ s hwf, machine2_pack]

theorem to_bytes3_canonical_call (a : Field.Serial) (s : GlobalState) (hwf : s.WF) :
    RIR.agave_serial_field_to_bytes_observe_3.call
      (RIR.agave_serial_field_to_bytes_observe_3.args
        (.value (a 0)) (.value (a 1)) (.value (a 2)) (.value (a 3)) (.value (a 4))) s =
      .value (.cons (.value (packWords (tightWords a) 3)) .nil, s) := by
  rw [RIR.to_bytes3_call _ _ _ _ _ s hwf, machine3_pack]

/-- The values returned by the four exact serialization observations determine
these affine compressed bytes. This theorem concerns their values; executing
the aggregate projective point-compression wrapper additionally requires its
inversion/multiplication refinement. -/
def machineAffineBytes (x y : Field.Serial) : BitVec 256 :=
  BitVec.ofNat 1 ((machineBytes x).toNat % 2) ++
    BitVec.ofNat 255 (machineBytes y).toNat

theorem machineAffineBytes_eq_compress (x y : Field.Serial) (P : CurvePoint)
    (hx : (Field.serialValue x : ZMod p) = P.x)
    (hy : (Field.serialValue y : ZMod p) = P.y) :
    machineAffineBytes x y = compress P := by
  unfold machineAffineBytes
  rw [machineBytes_eq_toBytes, machineBytes_eq_toBytes]
  exact serial_affine_compress x y P hx hy

theorem machineSplitAffineBytes_eq_compress (v : Field.Packed)
    (ex ey : Field.Element) (P : CurvePoint)
    (hx : (Field.packedValue v ex : ZMod p) = P.x)
    (hy : (Field.packedValue v ey : ZMod p) = P.y) :
    machineAffineBytes (Field.split v ex) (Field.split v ey) = compress P := by
  apply machineAffineBytes_eq_compress
  · simpa only [Field.split_value] using hx
  · simpa only [Field.split_value] using hy

end Agave.Ed25519.Encoding

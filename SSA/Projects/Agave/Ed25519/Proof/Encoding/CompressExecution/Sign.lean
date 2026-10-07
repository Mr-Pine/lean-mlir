import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Coordinates
import SSA.Projects.RIR.Run.Scalar

/-! The compressor's actual final-byte shift and disjoint OR. Canonical y
makes the flagged OR safe, including the x = 0 case. -/
namespace Agave.Ed25519.Encoding.Compress.Execution
open LeanMLIR.RIR

/-- The last byte calculation in registers 221–224, with black_box's
value-preserving result supplied by its separately proved execution theorem. -/
def insertSign (x y : BitVec 8) : BitVec 8 := ((x &&& 1) <<< 7) ||| y

theorem insertSign_disjoint (x y : BitVec 8) (hy : y[7] = false) :
    ((x &&& 1) <<< 7) &&& y = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;>
    simp [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
      BitVec.getLsbD_eq_getElem, hy]

/-- The emitted disjoint OR has no poison when y's top bit is clear. -/
theorem insertSign_operation (x y : BitVec 8) (hy : y[7] = false) :
    Operation.or true (.value ((x &&& 1) <<< 7)) (.value y) =
      .value (insertSign x y) := by
  have hd := insertSign_disjoint x y hy
  simp only [BitVec.ofNat_eq_ofNat] at hd
  simp [Operation.or, insertSign, hd]

/-- The byte assembled by the emitted instructions is byte 31 of the shared
bit-vector encoding. -/
theorem insertSign_lastByte (x : BitVec 8) (y : BitVec 256)
    (hy : y[255] = false) :
    insertSign x (y.extractLsb' 248 8) =
      ((x.extractLsb' 0 1) ++ y.extractLsb' 0 255).extractLsb' 248 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb']
  rw [BitVec.getLsbD_append]
  interval_cases i <;>
    simp [insertSign, BitVec.append_def, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
      BitVec.getLsbD_eq_getElem, hy]

/-- Canonical field serialization establishes exactly the high-bit condition
required by the emitted flagged OR. -/
theorem serialized_top_clear (y : Field.Serial) :
    (toBytes (fun i => (y i).toNat))[255] = false := by
  have hy := toBytes_canonical (fun i => (y i).toNat) (fun i => (y i).isLt)
  have hlt : (toBytes (fun i => (y i).toNat)).toNat < 2 ^ 255 := by
    have hm : modulus < 2 ^ 255 := by norm_num [modulus, top]
    omega
  rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_last]
  simpa using hlt

/-- Low bytes do not intersect the inserted sign bit. -/
theorem append_low_byte (sign : BitVec 1) (y : BitVec 256) (i : Nat) (hi : i < 31) :
    (sign ++ y.extractLsb' 0 255).extractLsb' (8 * i) 8 =
      y.extractLsb' (8 * i) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hlow : 8 * i + j < 255 := by omega
  simp only [BitVec.getLsbD_extractLsb']
  rw [BitVec.getLsbD_append]
  simp [hlow, hj, BitVec.getLsbD_extractLsb']

/-- The 32 emitted store values once the inline canonicalizers have completed. -/
def encodedBytes (x y : Field.Serial) (i : Fin 32) : BitVec 8 :=
  let xb := toBytes (fun j => (x j).toNat)
  let yb := toBytes (fun j => (y j).toNat)
  if i.val = 31 then insertSign (xb.extractLsb' 0 8) (yb.extractLsb' 248 8)
  else yb.extractLsb' (8 * i.val) 8

theorem serialized_concat_eq_compress (x y : Field.Serial) (P : Bridge.CurvePoint)
    (hx : (Field.serialValue x : K) = P.x) (hy : (Field.serialValue y : K) = P.y) :
    (toBytes (fun j => (x j).toNat)).extractLsb' 0 1 ++
      (toBytes (fun j => (y j).toNat)).extractLsb' 0 255 = Bridge.compress P := by
  have low (b : BitVec 256) (w : Nat) : b.extractLsb' 0 w = BitVec.ofNat w b.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_ofNat]
  rw [low, low]
  have parity (n : Nat) : BitVec.ofNat 1 n = BitVec.ofNat 1 (n % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp
  rw [parity]
  exact serial_affine_compress x y P hx hy

theorem encodedBytes_eq_compress (x y : Field.Serial) (P : Bridge.CurvePoint)
    (hx : (Field.serialValue x : K) = P.x) (hy : (Field.serialValue y : K) = P.y)
    (i : Fin 32) : encodedBytes x y i = (Bridge.compress P).extractLsb' (8 * i.val) 8 := by
  rw [← serialized_concat_eq_compress x y P hx hy]
  unfold encodedBytes
  split
  · rename_i hi
    rw [hi]
    rw [insertSign_lastByte _ _ (serialized_top_clear y)]
    rw [BitVec.extractLsb'_extractLsb'_of_le (by decide : 0 + 1 ≤ 8)]
  · rename_i hi
    exact (append_low_byte _ _ _ (by omega)).symm

end Agave.Ed25519.Encoding.Compress.Execution

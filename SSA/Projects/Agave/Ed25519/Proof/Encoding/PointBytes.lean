import SSA.Projects.Agave.Ed25519.Bridge.Encoding
import SSA.Projects.Agave.Ed25519.Proof.Encoding.FieldBytes

/-!
The point-encoding boundary. Agave's decompression first obtains an even
square root, then conditionally negates it using the sign bit. Negating zero
leaves zero, so both sign bits decode when x=0. Compression always writes
canonical y and canonical x parity. This module proves these facts in the
shared Edwards group; it does not assume a theorem about the sqrt routine or
about RIR execution of inversion, multiplication, or byte stores.
-/

namespace Agave.Ed25519.Encoding

open _root_.Ed25519 Bridge

/-- The point-level action of `decompress::step_2`. -/
def applySign (P : CurvePoint) (sign : Bool) : CurvePoint :=
  if sign then -P else P

@[simp] theorem applySign_y (P : CurvePoint) (sign : Bool) :
    (applySign P sign).y = P.y := by
  cases sign <;> simp [applySign, Edwards.Point.neg_y]

@[simp] theorem applySign_x_zero (P : CurvePoint) (hx : P.x = 0)
    (sign : Bool) : (applySign P sign).x = 0 := by
  cases sign <;> simp [applySign, Edwards.Point.neg_x, hx]

/-- The supplied sign is respected whenever the even root is nonzero. -/
theorem applySign_parity (P : CurvePoint) (heven : P.x.val % 2 = 0)
    (hx : P.x ≠ 0) (sign : Bool) :
    (applySign P sign).x.val % 2 = 0 ↔ sign = false := by
  cases sign
  · simp [applySign, heven]
  · change (-P.x).val % 2 = 0 ↔ true = false
    rw [ZMod.neg_val, if_neg hx]
    have hlt := ZMod.val_lt P.x
    have hp : p % 2 = 1 := by decide
    have hm := congrArg (fun n : Nat => n % 2)
      (Nat.sub_add_cancel (Nat.le_of_lt hlt))
    rw [Nat.add_mod, heven, hp, Nat.add_zero, Nat.mod_mod] at hm
    simp [hm]

/-- Once the square-root routine has returned a curve point with even x and
the decoded y, the actual sign-selection algorithm satisfies permissive
`Encodes` for every byte string, including noncanonical y and x=0. -/
theorem applySign_encodes (bytes : BitVec 256) (P : CurvePoint)
    (hy : P.y = ((bytes.extractLsb' 0 255).toNat : ZMod p))
    (heven : P.x.val % 2 = 0) :
    Encodes bytes (applySign P bytes[255]) := by
  constructor
  · simpa using hy
  · intro hx
    have hP : P.x ≠ 0 := fun hz => hx (applySign_x_zero P hz _)
    exact applySign_parity P heven hP _

/-- Zero-root sign ambiguity is real: changing only the sign does not
change the mathematical point. -/
theorem applySign_zero_eq (P : CurvePoint) (hx : P.x = 0) :
    applySign P true = applySign P false := by
  apply Edwards.Point.ext
  · simp [applySign_x_zero, hx]
  · simp

/-- Compression resolves the zero-root ambiguity by writing a zero sign bit. -/
theorem compress_zero_sign (P : CurvePoint) (hx : P.x = 0) :
    (compress P)[255] = false := by
  rw [compress_sign]
  simp [hx]

/-- Complete compression criterion, including the zero-root case omitted
from the verifier bridge because zero-root points are small order. -/
theorem compress_eq_iff_all (bytes : BitVec 256) (P : CurvePoint) :
    compress P = bytes ↔
      Encodes bytes P ∧ CanonicalY bytes ∧ (P.x = 0 → bytes[255] = false) := by
  constructor
  · rintro rfl
    exact ⟨compress_encodes P, compress_canonical P, compress_zero_sign P⟩
  · rintro ⟨henc, hcanonical, hzero⟩
    by_cases hx : P.x = 0
    · apply bytes_eq_of_parts
      · apply BitVec.eq_of_toNat_eq
        rw [compress_y]
        have hv := congrArg ZMod.val henc.1
        simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hcanonical] using hv
      · exact (compress_zero_sign P hx).trans (hzero hx).symm
    · exact (compress_eq_iff hx).2 ⟨henc, hcanonical⟩

/-- Canonical serialization of mathematical affine coordinates. The field
serializer theorem separately identifies its output with each coordinate's
canonical natural representative. -/
def affineBytes (x y : ZMod p) : BitVec 256 :=
  BitVec.ofNat 1 (x.val % 2) ++ BitVec.ofNat 255 y.val

theorem affineBytes_eq_compress (P : CurvePoint) :
    affineBytes P.x P.y = compress P := rfl

/-- The field serializer returns the canonical natural representative of the
represented field element, for every five-u64 representation. -/
theorem serial_toBytes_eq_field (a : Field.Serial) (z : ZMod p)
    (hz : (Field.serialValue a : ZMod p) = z) :
    (toBytes (fun i => (a i).toNat)).toNat = z.val := by
  rw [toBytes_toNat _ (fun i => (a i).isLt), value_eq_decode51]
  change Field.serialValue a % modulus = _
  have hv := congrArg ZMod.val hz
  rw [ZMod.val_natCast] at hv
  have hp : p = modulus := by norm_num [p, modulus, top]
  exact (congrArg (fun n : Nat => Field.serialValue a % n) hp.symm).trans hv

theorem serial_toBytes_eq_y (a : Field.Serial) (P : CurvePoint)
    (hy : (Field.serialValue a : ZMod p) = P.y) :
    (toBytes (fun i => (a i).toNat)).toNat = P.y.val :=
  serial_toBytes_eq_field a P.y hy

/-- The affine compressor's two field serializations and parity insertion
give the shared byte-level compression. Only representation equalities are
premises; no canonical-limb or nonzero-x premise is needed. -/
theorem serial_affine_compress (x y : Field.Serial) (P : CurvePoint)
    (hx : (Field.serialValue x : ZMod p) = P.x)
    (hy : (Field.serialValue y : ZMod p) = P.y) :
    BitVec.ofNat 1 ((toBytes (fun i => (x i).toNat)).toNat % 2) ++
      BitVec.ofNat 255 (toBytes (fun i => (y i).toNat)).toNat = compress P := by
  rw [serial_toBytes_eq_field x P.x hx, serial_toBytes_eq_field y P.y hy]
  rfl

/-- The AVX2 split has the identical observation when the packed lane
represents the same affine field coordinate. -/
theorem split_toBytes_eq_y (v : Field.Packed) (e : Field.Element) (P : CurvePoint)
    (hy : (Field.packedValue v e : ZMod p) = P.y) :
    (toBytes (fun i => (Field.split v e i).toNat)).toNat = P.y.val := by
  apply serial_toBytes_eq_y
  simpa only [Field.split_value] using hy

theorem split_affine_compress (v : Field.Packed) (ex ey : Field.Element)
    (P : CurvePoint) (hx : (Field.packedValue v ex : ZMod p) = P.x)
    (hy : (Field.packedValue v ey : ZMod p) = P.y) :
    BitVec.ofNat 1 ((toBytes (fun i => (Field.split v ex i).toNat)).toNat % 2) ++
      BitVec.ofNat 255 (toBytes (fun i => (Field.split v ey i).toNat)).toNat =
        compress P := by
  apply serial_affine_compress
  · simpa only [Field.split_value] using hx
  · simpa only [Field.split_value] using hy

end Agave.Ed25519.Encoding

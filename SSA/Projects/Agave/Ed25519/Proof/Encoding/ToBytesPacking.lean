import SSA.Projects.Agave.Ed25519.Proof.Encoding.ToBytesArithmetic
import SSA.Projects.Agave.Ed25519.Proof.Encoding.ToBytesMachine
import Init.Data.BitVec.Bitblast

namespace Agave.Ed25519.Encoding

theorem narrow51_widen (x : BitVec 64) :
    (x.setWidth 51).setWidth 64 = x &&& 2251799813685247 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat]

theorem narrow51_shift51 (x : BitVec 64) :
    ((x.setWidth 51).setWidth 64) <<< 51 = x <<< 51 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft]

theorem low51_disjoint_shift51 (x y : BitVec 64) :
    (x &&& 2251799813685247) &&& (y <<< 51) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat]

theorem split51_add (x : BitVec 64) :
    (x &&& 2251799813685247) + ((x >>> 51) <<< 51) = x := by
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ (low51_disjoint_shift51 x (x >>> 51))]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;>
    simp [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat]

/-- LLVM omits the first carry/mask when emitting the low output u64. The
omission is valid for every two input words, including wrapping additions. -/
theorem first_word_pack (x y : BitVec 64) :
    x + (y <<< 51) = (x.setWidth 51).setWidth 64 |||
      (((y + (x >>> 51)).setWidth 51).setWidth 64) <<< 51 := by
  rw [narrow51_widen, narrow51_shift51]
  calc
    x + (y <<< 51) =
        ((x &&& 2251799813685247) + ((x >>> 51) <<< 51)) + (y <<< 51) := by
      rw [split51_add]
    _ = (x &&& 2251799813685247) + ((y + (x >>> 51)) <<< 51) := by
      rw [BitVec.shiftLeft_add_distrib]
      rw [BitVec.add_assoc, BitVec.add_comm ((x >>> 51) <<< 51) (y <<< 51)]
    _ = _ := BitVec.add_eq_or_of_and_eq_zero _ _ (low51_disjoint_shift51 _ _)

def emittedPack1 (x y : BitVec 64) : BitVec 64 :=
  let a := x >>> 13
  let boundary := ((y <<< 6) &&& 192) ||| ((x >>> 45) &&& 63)
  (((a &&& 4294967040) ||| ((y <<< 38) &&& 18446742974197923840)) |||
    (boundary <<< 32)) ||| (a &&& 255)

def emittedPack2 (x y : BitVec 64) : BitVec 64 :=
  let a := x >>> 26
  let boundary := ((y <<< 1) &&& 254) ||| ((x >>> 50) &&& 1)
  (((a &&& 16776960) ||| ((y <<< 25) &&& 18446744069414584320)) |||
    (boundary <<< 24)) ||| (a &&& 255)

def emittedPack3 (x y : BitVec 64) : BitVec 64 :=
  let boundary := ((y <<< 4) &&& 240) ||| ((x >>> 47) &&& 15)
  (((y <<< 12) &&& 9223372036854710272) ||| (boundary <<< 8)) ||| ((x >>> 39) &&& 255)

theorem emittedPack1_eq (x y : BitVec 64) :
    emittedPack1 x y = ((x.setWidth 51).setWidth 64 >>> 13) |||
      ((y.setWidth 51).setWidth 64 <<< 38) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;>
    simp [emittedPack1, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, BitVec.getLsbD_of_ge]

theorem emittedPack2_eq (x y : BitVec 64) :
    emittedPack2 x y = ((x.setWidth 51).setWidth 64 >>> 26) |||
      ((y.setWidth 51).setWidth 64 <<< 25) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;>
    simp [emittedPack2, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, BitVec.getLsbD_of_ge]

theorem emittedPack3_eq (x y : BitVec 64) :
    emittedPack3 x y = ((x.setWidth 51).setWidth 64 >>> 39) |||
      ((y.setWidth 51).setWidth 64 <<< 12) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;>
    simp [emittedPack3, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, BitVec.getLsbD_of_ge]

end Agave.Ed25519.Encoding

import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.MachineArithmetic5
import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.MachineShift
import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.PackingBits
import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.InputDigits

namespace Firedancer.Common.ScalarArithmetic
open LeanMLIR SLLVM
open InstCombine (LLVM)
open R43x6 (FitsLong)
open IntegerRegisters MachineArithmetic

/-- The twelve signed limbs consumed by the exact source packing sequence. -/
def packingInputs (d : Digits) : Fin 12 → BitVec 64 := ![
  BitVec.ofInt 64 (z413 d), BitVec.ofInt 64 (z425 d), BitVec.ofInt 64 (z428 d), BitVec.ofInt 64 (z430 d), BitVec.ofInt 64 (z432 d), BitVec.ofInt 64 (z434 d), BitVec.ofInt 64 (z436 d), BitVec.ofInt 64 (z438 d), BitVec.ofInt 64 (z440 d), BitVec.ofInt 64 (z442 d), BitVec.ofInt 64 (z444 d), BitVec.ofInt 64 (z446 d)]

theorem inputMatches (digest : BitVec 512) : InputMatches digest (inputDigits digest) := by
  constructor
  · exact Registers.r61_value digest
  · exact Registers.r63_value digest
  · exact Registers.r65_value digest
  · exact Registers.r67_value digest
  · exact Registers.r69_value digest
  · exact Registers.r71_value digest
  · exact Registers.r73_value digest
  · exact Registers.r75_value digest
  · exact Registers.r77_value digest
  · exact Registers.r79_value digest
  · exact Registers.r81_value digest
  · exact Registers.r83_value digest
  · exact Registers.r85_value digest
  · exact Registers.r87_value digest
  · exact Registers.r89_value digest
  · exact Registers.r91_value digest
  · exact Registers.r93_value digest
  · exact Registers.r95_value digest
  · exact Registers.r97_value digest
  · exact Registers.r99_value digest
  · exact Registers.r101_value digest
  · exact Registers.r103_value digest
  · exact Registers.r105_value digest
  · exact Registers.r106_value digest

namespace Registers
set_option maxHeartbeats 2000000

theorem packedShift468 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : r468 digest = .value (BitVec.ofInt 64 (z438 d) <<< (19 : Nat)) := by
  rw [r468, value438 digest d hd hm, r9]
  apply shl_nsw_ofInt (z438_fits d hd) ?_ (by decide)
  have hb := z438_bounds d hd
  norm_num [FitsLong]
  omega

theorem packedShift471 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : r471 digest = .value (BitVec.ofInt 64 (z440 d) <<< (40 : Nat)) := by
  rw [r471, value440 digest d hd hm, r1]
  apply shl_nsw_ofInt (z440_fits d hd) ?_ (by decide)
  have hb := z440_bounds d hd
  norm_num [FitsLong]
  omega

theorem packedShift479 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : r479 digest = .value (BitVec.ofInt 64 (z444 d) <<< (18 : Nat)) := by
  rw [r479, value444 digest d hd hm, r11]
  apply shl_nsw_ofInt (z444_fits d hd) ?_ (by decide)
  have hb := z444_bounds d hd
  norm_num [FitsLong]
  omega

theorem packedShift482 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : r482 digest = .value (BitVec.ofInt 64 (z446 d) <<< (39 : Nat)) := by
  rw [r482, value446 digest d hd hm, r12]
  apply shl_nsw_ofInt (z446_fits d hd) ?_ (by decide)
  have hb := z446_bounds d hd
  norm_num [FitsLong]
  omega

theorem reduce_eq_packingWords (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : reduce digest = some (packingWords (packingInputs d)) := by
  unfold reduce
  simp only [
    packedShift468 digest d hd hm,
    packedShift471 digest d hd hm,
    packedShift479 digest d hd hm,
    packedShift482 digest d hd hm,
    r447,
    r448,
    r449,
    r450,
    r451,
    r452,
    r453,
    r454,
    r455,
    r456,
    r457,
    r458,
    r459,
    r460,
    r461,
    r462,
    r463,
    r464,
    r466,
    r467,
    r469,
    r470,
    r472,
    r473,
    r474,
    r475,
    r477,
    r478,
    r480,
    r481,
    r483,
    r426,
    value413 digest d hd hm,
    value425 digest d hd hm,
    value428 digest d hd hm,
    value430 digest d hd hm,
    value432 digest d hd hm,
    value434 digest d hd hm,
    value436 digest d hd hm,
    value438 digest d hd hm,
    value440 digest d hd hm,
    value442 digest d hd hm,
    value444 digest d hd hm,
    value446 digest d hd hm,
    r0,
    r1,
    r2,
    r3,
    r4,
    r5,
    r6,
    r7,
    r8,
    r9,
    r10,
    r11,
    r12,
    r13,
    r14,
    r15,
    r16,
    r17,
    r18,
    r19,
    r20,
    r21,
    r22,
    r23,
    r24,
    r25,
    r26,
    r27,
    r28,
    r29,
    r30,
    r31,
    r32,
    r33,
    r34,
    r35,
    r36,
    r37,
    r38,
    r39,
    r40,
    r41,
    r42,
    r43,
    r44,
    r45]
  rfl

end Registers
end Firedancer.Common.ScalarArithmetic

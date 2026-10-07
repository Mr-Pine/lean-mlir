import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryPart1
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.UpperPacking

/-! Word expressions in exactly the source's operation order, and local bridges
between a bounded natural cancellation input and its machine representation. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open LeanMLIR.RIR
open Agave.Ed25519.ScalarReduce32.Arithmetic
set_option maxRecDepth 100000

/-- The source adds its adjustment product before the input sum. -/
def sourceCarryWord (sum : BitVec 128) : BitVec 128 :=
  ((digitWord sum).setWidth 128 * 671914833335277#128 + sum) >>> (52 : Nat)

theorem sourceCarryWord_eq (sum : BitVec 128) : sourceCarryWord sum = carryWord sum := by
  simp only [sourceCarryWord, carryWord, BitVec.add_comm]

def wordCancellationSums (z : Fin 9 → BitVec 128) (i : Fin 5) : BitVec 128 :=
  match i.val with
  | 0 => z 0
  | 1 =>
      let w0 := z 0
      (digitWord w0).setWidth 128 * 3916664325105025#128 + z 1 + sourceCarryWord w0
  | 2 =>
      let w0 := z 0
      let w1 := (digitWord w0).setWidth 128 * 3916664325105025#128 + z 1 + sourceCarryWord w0
      z 2 + (digitWord w0).setWidth 128 * 1367801#128 +
        (digitWord w1).setWidth 128 * 3916664325105025#128 + sourceCarryWord w1
  | 3 =>
      let w0 := z 0
      let w1 := (digitWord w0).setWidth 128 * 3916664325105025#128 + z 1 + sourceCarryWord w0
      let w2 := z 2 + (digitWord w0).setWidth 128 * 1367801#128 +
        (digitWord w1).setWidth 128 * 3916664325105025#128 + sourceCarryWord w1
      (digitWord w1).setWidth 128 * 1367801#128 + z 3 +
        (digitWord w2).setWidth 128 * 3916664325105025#128 + sourceCarryWord w2
  | _ =>
      let w0 := z 0
      let w1 := (digitWord w0).setWidth 128 * 3916664325105025#128 + z 1 + sourceCarryWord w0
      let w2 := z 2 + (digitWord w0).setWidth 128 * 1367801#128 +
        (digitWord w1).setWidth 128 * 3916664325105025#128 + sourceCarryWord w1
      let w3 := (digitWord w1).setWidth 128 * 1367801#128 + z 3 +
        (digitWord w2).setWidth 128 * 3916664325105025#128 + sourceCarryWord w2
      z 4 + ((digitWord w0).setWidth 128 <<< (44 : Nat)) +
        (digitWord w2).setWidth 128 * 1367801#128 +
        (digitWord w3).setWidth 128 * 3916664325105025#128 + sourceCarryWord w3

def wordUpperSums (z : Fin 9 → BitVec 128) (i : Fin 4) : BitVec 128 :=
  let w := wordCancellationSums z
  let n := fun i => (digitWord (w i)).setWidth 128
  match i.val with
  | 0 => (n 1 <<< (44 : Nat)) + z 5 + n 3 * 1367801#128 +
      n 4 * 3916664325105025#128 + sourceCarryWord (w 4)
  | 1 =>
      let q0 := (n 1 <<< (44 : Nat)) + z 5 + n 3 * 1367801#128 +
        n 4 * 3916664325105025#128 + sourceCarryWord (w 4)
      (n 2 <<< (44 : Nat)) + z 6 + n 4 * 1367801#128 + (q0 >>> (52 : Nat))
  | 2 =>
      let q0 := (n 1 <<< (44 : Nat)) + z 5 + n 3 * 1367801#128 +
        n 4 * 3916664325105025#128 + sourceCarryWord (w 4)
      let q1 := (n 2 <<< (44 : Nat)) + z 6 + n 4 * 1367801#128 + (q0 >>> (52 : Nat))
      (n 3 <<< (44 : Nat)) + z 7 + (q1 >>> (52 : Nat))
  | _ =>
      let q0 := (n 1 <<< (44 : Nat)) + z 5 + n 3 * 1367801#128 +
        n 4 * 3916664325105025#128 + sourceCarryWord (w 4)
      let q1 := (n 2 <<< (44 : Nat)) + z 6 + n 4 * 1367801#128 + (q0 >>> (52 : Nat))
      let q2 := (n 3 <<< (44 : Nat)) + z 7 + (q1 >>> (52 : Nat))
      (n 4 <<< (44 : Nat)) + z 8 + (q2 >>> (52 : Nat))

def wordQuotientLimbs (z : Fin 9 → BitVec 128) (i : Fin 5) : BitVec 64 :=
  match i.val with
  | 0 => (wordUpperSums z 0).setWidth 64 &&& 4503599627370495#64
  | 1 => (wordUpperSums z 1).setWidth 64 &&& 4503599627370495#64
  | 2 => (wordUpperSums z 2).setWidth 64 &&& 4503599627370495#64
  | 3 => (wordUpperSums z 3).setWidth 64 &&& 4503599627370495#64
  | _ => ((wordUpperSums z 3) >>> (52 : Nat)).setWidth 64

theorem word_repr (word : BitVec width) : word = BitVec.ofNat width word.toNat :=
  (BitVec.toNat_eq_nat.mp rfl).2

/-- A word/natural input equality transports the masked Montgomery digit. -/
theorem digitWord_repr (word : BitVec 128) (value : Nat) (h : word.toNat = value) :
    (digitWord word).setWidth 128 = BitVec.ofNat 128 (adjustmentDigit value) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128), digitWord_toNat, h,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((adjustmentDigit_bound value).trans (by decide))]

/-- The local bound established for every cancellation input removes the
machine wrap and yields the exact natural Montgomery carry. -/
theorem sourceCarryWord_repr (word : BitVec 128) (value : Nat)
    (h : word.toNat = value) (hv : value < 2 ^ 120) :
    sourceCarryWord word = BitVec.ofNat 128 (adjustmentCarry value) := by
  apply BitVec.eq_of_toNat_eq
  rw [sourceCarryWord_eq, carryWord_toNat word (by simpa only [h] using hv), h,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((adjustmentCarry_bound120 value hv).trans (by decide))]

/-- A represented bounded value survives a u128 left shift as modular multiplication. -/
theorem ofNat_shift44 (value : Nat) (h : value < 2 ^ 128) :
    (BitVec.ofNat 128 value <<< (44 : Nat)) = BitVec.ofNat 128 (value * 17592186044416) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.shiftLeft_eq]

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

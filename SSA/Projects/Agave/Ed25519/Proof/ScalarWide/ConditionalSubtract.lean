import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Arithmetic

/-! The shared five-limb Scalar52 conditional subtraction. This is the exact
wrapping-word borrow/addback calculation used in both extracted scalar reducers.
Packing is by 52-bit limbs, not by 64-bit memory slots. The separate RIR phase
proof must also discharge each retained poison flag and the black-box call. -/

namespace Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction

open Agave.Ed25519.Bridge

abbrev Limbs := Fin 5 → BitVec 64

/-- The five raw differences, whose sign bits carry the borrow. -/
def differences (x0 x1 x2 x3 x4 : BitVec 52) (i : Fin 5) : BitVec 64 :=
  match i.val with
  | 0 => x0.setWidth 64 + (-671914833335277 : BitVec 64)
  | 1 =>
      let d0 := x0.setWidth 64 + (-671914833335277 : BitVec 64)
      d0.sshiftRight 63 + (-3916664325105025 : BitVec 64) + x1.setWidth 64
  | 2 =>
      let d0 := x0.setWidth 64 + (-671914833335277 : BitVec 64)
      let d1 := d0.sshiftRight 63 + (-3916664325105025 : BitVec 64) + x1.setWidth 64
      d1.sshiftRight 63 + (-1367801 : BitVec 64) + x2.setWidth 64
  | 3 =>
      let d0 := x0.setWidth 64 + (-671914833335277 : BitVec 64)
      let d1 := d0.sshiftRight 63 + (-3916664325105025 : BitVec 64) + x1.setWidth 64
      let d2 := d1.sshiftRight 63 + (-1367801 : BitVec 64) + x2.setWidth 64
      x3.setWidth 64 + d2.sshiftRight 63
  | _ =>
      let d0 := x0.setWidth 64 + (-671914833335277 : BitVec 64)
      let d1 := d0.sshiftRight 63 + (-3916664325105025 : BitVec 64) + x1.setWidth 64
      let d2 := d1.sshiftRight 63 + (-1367801 : BitVec 64) + x2.setWidth 64
      let d3 := x3.setWidth 64 + d2.sshiftRight 63
      x4.setWidth 64 + (-17592186044416 : BitVec 64) + d3.sshiftRight 63

/-- Exact byte passed through the subtle black-box identity. -/
def borrowByte (d : Limbs) : BitVec 8 := (d 4 >>> 63).setWidth 8

/-- Add back L precisely when the subtraction borrowed. All five output words
are masked, including the top word, as in the imported body. -/
def addback (d : Limbs) : Limbs :=
  let mask := (0 : BitVec 64) - (borrowByte d).setWidth 64
  let t0 := (d 0 &&& 4503599627370495#64) + (mask &&& 671914833335277#64)
  let t1 := (t0 >>> 52) + (mask &&& 3916664325105025#64) +
    (d 1 &&& 4503599627370495#64)
  let t2 := (d 2 &&& 4503599627370495#64) + (mask &&& 1367801#64) + (t1 >>> 52)
  let t3 := (t2 >>> 52) + (d 3 &&& 4503599627370495#64)
  let t4 := d 4 + (mask &&& 17592186044416#64) + (t3 >>> 52)
  ![t0 &&& 4503599627370495#64, t1 &&& 4503599627370495#64,
    t2 &&& 4503599627370495#64, t3 &&& 4503599627370495#64,
    t4 &&& 4503599627370495#64]

def packed (x0 x1 x2 x3 x4 : BitVec 52) : BitVec 260 :=
  x4 ++ x3 ++ x2 ++ x1 ++ x0

def packedOutput (words : Limbs) : BitVec 260 :=
  packed ((words 0).setWidth 52) ((words 1).setWidth 52)
    ((words 2).setWidth 52) ((words 3).setWidth 52) ((words 4).setWidth 52)

/-- One radix-52 subtraction digit and its outgoing borrow. -/
def subtractDigit (a b incoming : Nat) : Nat × Nat :=
  if a < b + incoming then (a + 2 ^ 52 - (b + incoming), 1)
  else (a - (b + incoming), 0)

/-- Algebraic invariant of a single subtraction digit. -/
theorem subtractDigit_equation (a b incoming : Nat)
    (ha : a < 2 ^ 52) (hb : b < 2 ^ 52) (hin : incoming ≤ 1) :
    a + 2 ^ 52 * (subtractDigit a b incoming).2 =
      b + incoming + (subtractDigit a b incoming).1 ∧
      (subtractDigit a b incoming).1 < 2 ^ 52 ∧
      (subtractDigit a b incoming).2 ≤ 1 := by
  unfold subtractDigit
  split_ifs with h <;> dsimp <;> omega

/-- The packed borrow invariant determines the exact conditional-subtraction
result. This is proved with integer bounds; the word bridge must establish
this invariant from the machine's five local borrow steps. -/
theorem conditional_addback_identity (raw difference : Nat) (borrow : Bool)
    (hraw : raw < 2 ^ 260) (hdifference : difference < 2 ^ 260)
    (hborrow : raw + (if borrow then 2 ^ 260 else 0) = subgroupOrder + difference) :
    (difference + (if borrow then subgroupOrder else 0)) % 2 ^ 260 =
      if raw < subgroupOrder then raw else raw - subgroupOrder := by
  cases borrow with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hborrow ⊢
      rw [Nat.mod_eq_of_lt hdifference]
      have hn : ¬ raw < subgroupOrder := by omega
      rw [if_neg hn]
      omega
  | true =>
      simp only [↓reduceIte] at hborrow ⊢
      have hlt : raw < subgroupOrder := by omega
      have he : difference + subgroupOrder = raw + 2 ^ 260 := by omega
      rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt hraw, if_pos hlt]

end Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction

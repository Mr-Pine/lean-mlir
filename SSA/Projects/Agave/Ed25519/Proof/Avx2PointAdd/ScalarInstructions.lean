import SSA.Projects.RIR.Semantics.Operations.Scalar
import Mathlib.Tactic

/-! Signed-overflow obligations of the emitted packed `diff_sum` instructions.
The hypotheses are deliberately weaker than the reduced-limb invariant. -/
namespace Agave.Ed25519.Avx2PointAdd
open LeanMLIR.RIR

theorem sub32_small_flags (x y : BitVec 32)
    (hx : x.toNat < 2^28) (hy : y.toNat < 2^28) :
    x.ssubOverflow y = false := by
  have hxi : x.toInt = (x.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hyi : y.toInt = (y.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  simp only [BitVec.ssubOverflow, hxi, hyi, Bool.or_eq_false_iff,
    decide_eq_false_iff_not]
  constructor <;> norm_num <;> omega

theorem add32_small_flags (x y : BitVec 32)
    (hx : x.toNat < 2^28) (hy : y.toNat < 2^28) :
    x.saddOverflow y = false := by
  have hxi : x.toInt = (x.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hyi : y.toInt = (y.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  simp only [BitVec.saddOverflow, hxi, hyi, Bool.or_eq_false_iff,
    decide_eq_false_iff_not]
  constructor <;> norm_num <;> omega

theorem diff32_small_flags (c x y : BitVec 32)
    (hc : c.toNat < 2^28) (hx : x.toNat < 2^28) (hy : y.toNat < 2^28) :
    (c - x).saddOverflow y = false := by
  have hci : c.toInt = (c.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hxi : x.toInt = (x.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hyi : y.toInt = (y.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hsub : (c - x).toInt = c.toInt - x.toInt :=
    BitVec.toInt_sub_of_not_ssubOverflow (by simp [sub32_small_flags c x hc hx])
  simp only [BitVec.saddOverflow, hsub, hci, hxi, hyi, Bool.or_eq_false_iff,
    decide_eq_false_iff_not]
  constructor <;> norm_num <;> omega

theorem sub32_small_value (signed : Bool) (x y : BitVec 32)
    (hx : x.toNat < 2^28) (hy : y.toNat < 2^28) :
    Operation.sub {nsw := signed} (.value x) (.value y) = .value (x - y) := by
  simp [Operation.sub, sub32_small_flags x y hx hy]

theorem add32_small_value (signed : Bool) (x y : BitVec 32)
    (hx : x.toNat < 2^28) (hy : y.toNat < 2^28) :
    Operation.add {nsw := signed} (.value x) (.value y) = .value (x + y) := by
  simp [Operation.add, add32_small_flags x y hx hy]

theorem diff32_small_value (signed : Bool) (c x y : BitVec 32)
    (hc : c.toNat < 2^28) (hx : x.toNat < 2^28) (hy : y.toNat < 2^28) :
    Operation.add {nsw := signed} (.value (c - x)) (.value y) =
      .value ((c - x) + y) := by
  simp [Operation.add, diff32_small_flags c x y hc hx hy]

theorem mask32_small (x m : BitVec 32) (hm : m.toNat < 2^28) :
    (x &&& m).toNat < 2^28 := by
  rw [BitVec.toNat_and]
  exact Nat.and_le_right.trans_lt hm

theorem sub32_mask_value (signed : Bool) (c x m : BitVec 32)
    (hc : c.toNat < 2^28) (hm : m.toNat < 2^28) :
    Operation.sub {nsw := signed} (.value c) (.value (x &&& m)) =
      .value (c - (x &&& m)) :=
  sub32_small_value signed c (x &&& m) hc (mask32_small x m hm)

theorem add32_mask_value (signed : Bool) (x y m n : BitVec 32)
    (hm : m.toNat < 2^28) (hn : n.toNat < 2^28) :
    Operation.add {nsw := signed} (.value (x &&& m)) (.value (y &&& n)) =
      .value ((x &&& m) + (y &&& n)) :=
  add32_small_value signed (x &&& m) (y &&& n)
    (mask32_small x m hm) (mask32_small y n hn)

theorem diff32_mask_value (signed : Bool) (c x y m n : BitVec 32)
    (hc : c.toNat < 2^28) (hm : m.toNat < 2^28) (hn : n.toNat < 2^28) :
    Operation.add {nsw := signed} (.value (c - (x &&& m))) (.value (y &&& n)) =
      .value ((c - (x &&& m)) + (y &&& n)) :=
  diff32_small_value signed c (x &&& m) (y &&& n) hc
    (mask32_small x m hm) (mask32_small y n hn)

theorem sub_value (x y : BitVec w) :
    Operation.sub {} (.value x) (.value y) = .value (x - y) := by
  simp [Operation.sub]

end Agave.Ed25519.Avx2PointAdd

/-- info: 'Agave.Ed25519.Avx2PointAdd.sub32_mask_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.sub32_mask_value

/-- info: 'Agave.Ed25519.Avx2PointAdd.add32_mask_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.add32_mask_value

/-- info: 'Agave.Ed25519.Avx2PointAdd.diff32_mask_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.diff32_mask_value

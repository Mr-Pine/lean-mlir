import SSA.Projects.Agave.Ed25519.Proof.Tables.ConstructorConstant
import SSA.Projects.Agave.Ed25519.Proof.Tables.Dynamic
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.DoubleWord
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.PointLayout

/-!
The limb and word schedules of the serial table constructor. The initial
cache and all seven successor caches share the same conversion. This module
proves the representation invariant that an execution proof must maintain;
it does not identify an assumed successful execution with the constructor.
-/
namespace Agave.Ed25519.Tables.SerialConstructorArithmetic
open SerialFieldMul SerialPoint PointArithmetic
local instance : Fact (Nat.Prime modulus) := ⟨prime_p⟩

/-- Logical cache order; physical memory stores the first two fields reversed. -/
def cache (P : LimbPoint) : LimbPoint :=
  ⟨sub P.Y P.X, add P.X P.Y, P.Z, mul P.T serialD2Limbs⟩

theorem cache_bounded (P : LimbPoint) (h : PointTight P) : PointBounded (cache P) := by
  have hb := pointTight_bounded P h
  exact ⟨tight_bounded _ (sub_safe _ _ hb.2.1 hb.1).2.2,
    add_bounded _ _ h.1 h.2.1, hb.2.2.1,
    tight_bounded _ (mul_tight _ _ hb.2.2.2 (tight_bounded _ serialD2_tight))⟩

theorem cache_value (P : LimbPoint) (h : PointTight P) :
    pointValue (cache P) = serialCache (K := ZMod modulus) _root_.Ed25519.d (pointValue P) := by
  have hx := (pointTight_bounded P h).1
  have hd2 : value serialD2Limbs = (2 * (show ZMod modulus from _root_.Ed25519.d) : ZMod modulus) := serialD2_value
  ext <;> simp only [cache, pointValue, serialCache, sub_value _ _ hx,
    add_value, mul, mul_value, hd2] <;> ring

/-- Actual field-word computation, including the weak carry and pinned 2d multiply. -/
def cacheWord (P : WordPoint) : WordPoint :=
  ⟨subWord P.Y P.X, addWord P.X P.Y, P.Z, machine P.T serialD2Words⟩

theorem cacheWord_unsigned (P : WordPoint) (h : PointTight (unsignedPoint P)) :
    unsignedPoint (cacheWord P) = cache (unsignedPoint P) := by
  have hb := pointTight_bounded _ h
  change Bounded (unsigned P.X) ∧ Bounded (unsigned P.Y) ∧
    Bounded (unsigned P.Z) ∧ Bounded (unsigned P.T) at hb
  apply Extended.ext
  · exact subWord_unsigned _ _ hb.2.1 hb.1
  · exact addWord_unsigned _ _ hb.1 hb.2.1
  · rfl
  · exact machine_unsigned_mul _ _ hb.2.2.2 (tight_bounded _ serialD2_tight)

abbrev double (P : LimbPoint) : LimbPoint := asExtended (doubleCompleted P)

def step (D C : LimbPoint) : LimbPoint := cache (asExtended (cachedAddCompleted D C))

/-- The runtime loop keeps the double fixed and reads only the previous cache. -/
def entries (A : LimbPoint) : Nat → LimbPoint
  | 0 => cache A
  | k + 1 => step (double A) (entries A k)

theorem entries_bounded (A : LimbPoint) (h : PointTight A) (k : Nat) :
    PointBounded (entries A k) := by
  induction k with
  | zero => exact cache_bounded A h
  | succ k ih => exact cache_bounded _ (cachedAdd_tight _ _ (double_tight A h) ih)

theorem entries_value (A : LimbPoint) (h : PointTight A) (k : Nat) :
    pointValue (entries A k) = serialCache (K := ZMod modulus) _root_.Ed25519.d
      (serialOdd (K := ZMod modulus) _root_.Ed25519.d (pointValue A) k) := by
  induction k with
  | zero => exact cache_value A h
  | succ k ih =>
      change pointValue (cache (asExtended (cachedAddCompleted (double A) (entries A k)))) = _
      rw [cache_value _ (cachedAdd_tight _ _ (double_tight A h) (entries_bounded A h k)),
        cachedAdd_value _ _ (double_tight A h) (entries_bounded A h k), ih]
      rw [show pointValue (double A) = serialDouble (pointValue A) from double_value A h]
      rfl

/-- Finite output contract of the limb recurrence, independently of group membership. -/
theorem width5 (A : LimbPoint) (h : PointTight A) (k : Fin 8) :
    PointBounded (entries A k.val) ∧
      pointValue (entries A k.val) = serialCache (K := ZMod modulus) _root_.Ed25519.d
        (serialWidth5 (K := ZMod modulus) _root_.Ed25519.d (pointValue A) k) :=
  ⟨entries_bounded A h k.val, entries_value A h k.val⟩

def doubleWord (A : WordPoint) : WordPoint := asExtendedWord (SerialPoint.doubleWord A)

def stepWord (D C : WordPoint) : WordPoint :=
  cacheWord (asExtendedWord (cachedAddWord D C))

def entriesWord (A : WordPoint) : Nat → WordPoint
  | 0 => cacheWord A
  | k + 1 => stepWord (doubleWord A) (entriesWord A k)

theorem doubleWord_unsigned (A : WordPoint) (h : PointTight (unsignedPoint A)) :
    unsignedPoint (doubleWord A) = double (unsignedPoint A) := by
  rw [doubleWord, asExtendedWord_unsigned _ (SerialPoint.doubleWord_bounded A h),
    SerialPoint.doubleWord_unsigned A h]

theorem stepWord_unsigned (D C : WordPoint)
    (hd : PointTight (unsignedPoint D)) (hc : PointBounded (unsignedPoint C)) :
    unsignedPoint (stepWord D C) = step (unsignedPoint D) (unsignedPoint C) := by
  have hb : PointBounded (unsignedPoint (cachedAddWord D C)) := by
    rw [cachedAddWord_unsigned D C hd hc]
    exact cachedAddCompleted_bounded _ _ hd hc
  rw [stepWord, cacheWord_unsigned _ (asExtendedWord_tight _ hb),
    asExtendedWord_unsigned _ hb, cachedAddWord_unsigned D C hd hc]
  rfl

theorem entriesWord_unsigned (A : WordPoint) (h : PointTight (unsignedPoint A)) (k : Nat) :
    unsignedPoint (entriesWord A k) = entries (unsignedPoint A) k := by
  induction k with
  | zero => exact cacheWord_unsigned A h
  | succ k ih =>
      have hd : PointTight (unsignedPoint (doubleWord A)) := by
        rw [doubleWord_unsigned A h]
        exact double_tight _ h
      have hc : PointBounded (unsignedPoint (entriesWord A k)) := by
        rw [ih]
        exact entries_bounded _ h k
      rw [entriesWord, stepWord_unsigned _ _ hd hc, doubleWord_unsigned A h, ih]
      rfl

/-- Reorder logical cache words to exactly the Rust ProjectiveNiels record. -/
def cacheToWords (P : WordPoint) : SerialPoint.Execution.PointWords :=
  SerialPoint.Execution.pointToWords ⟨P.Y, P.X, P.Z, P.T⟩

@[simp] theorem cacheFromWords_toWords (P : WordPoint) :
    SerialPoint.Execution.cacheFromWords (cacheToWords P) = P := by
  simp only [cacheToWords, SerialPoint.Execution.cacheFromWords,
    SerialPoint.Execution.pointFromWords_toWords]

/-- Final physical records have the complete constructor representation contract. -/
theorem width5_words (A : WordPoint) (h : PointTight (unsignedPoint A)) (k : Fin 8) :
    let C := unsignedPoint (SerialPoint.Execution.cacheFromWords
      (cacheToWords (entriesWord A k.val)))
    PointBounded C ∧ pointValue C = serialCache (K := ZMod modulus) _root_.Ed25519.d
      (serialWidth5 (K := ZMod modulus) _root_.Ed25519.d (pointValue (unsignedPoint A)) k) := by
  dsimp only
  rw [cacheFromWords_toWords, entriesWord_unsigned A h k.val]
  exact width5 _ h k

end Agave.Ed25519.Tables.SerialConstructorArithmetic

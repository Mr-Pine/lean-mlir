import Mathlib.Data.BitVec
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Ring

/-!
Byte-level facts for the Ed25519 challenge, independent of either SHA-512
implementation. Bytes are ordered as they occur in memory; in particular the
first digest byte is the *least* significant byte of the scalar input. SHA-512's
internal big-endian word convention does not reverse this byte sequence.

`bytesOf` deliberately has the same definition as
`Firedancer.Common.bytesOf`, without importing its external SHA declarations.
The identity with the existing specification is checked in
`ChallengeFiredancer.lean`.
-/

namespace Agave.Ed25519.Bridge.Challenge

abbrev Bytes := List (BitVec 8)

/-- A byte list interpreted as a little-endian natural number. -/
def decodeLE : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * decodeLE bs

/-- Exactly `n` low bytes of an integer, least significant first. -/
def encodeLE : Nat → Nat → Bytes
  | 0, _ => []
  | n + 1, x => BitVec.ofNat 8 x :: encodeLE n (x / 256)

/-- The complete byte representation of a byte-aligned bitvector. -/
def bytesOf {n : Nat} (w : BitVec (n * 8)) : Bytes :=
  List.ofFn fun i : Fin n => w.extractLsb' (i * 8) 8

@[simp] theorem length_encodeLE (n x : Nat) : (encodeLE n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [encodeLE, ih]

@[simp] theorem length_bytesOf {n : Nat} (w : BitVec (n * 8)) :
    (bytesOf w).length = n := by
  simp [bytesOf]

theorem radix_pow (n : Nat) : 256 ^ n = 2 ^ (n * 8) := by
  rw [Nat.mul_comm n 8, pow_mul]
  rfl

theorem encodeLE_eq_ofFn (n x : Nat) :
    encodeLE n x = List.ofFn (fun i : Fin n => BitVec.ofNat 8 (x / 256 ^ i.val)) := by
  induction n generalizing x with
  | zero => simp [encodeLE]
  | succ n ih =>
      simp only [encodeLE, List.ofFn_succ, Fin.val_zero, pow_zero, Nat.div_one]
      congr 1
      rw [ih]
      congr 1
      funext i
      simp only [Fin.val_succ, Nat.div_div_eq_div_mul, pow_succ']

theorem bytesOf_eq_encodeLE {n : Nat} (w : BitVec (n * 8)) :
    bytesOf w = encodeLE n w.toNat := by
  rw [encodeLE_eq_ofFn]
  unfold bytesOf
  congr 1
  funext i
  simp only [BitVec.extractLsb', Nat.shiftRight_eq_div_pow, radix_pow]

/-- Byte assembly recovers exactly the low `8*n` bits, including leading
zero bytes. No boundedness premise is needed for the integer being encoded. -/
@[simp] theorem decodeLE_encodeLE (n x : Nat) :
    decodeLE (encodeLE n x) = x % 256 ^ n := by
  induction n generalizing x with
  | zero =>
      change 0 = x % 1
      exact (Nat.mod_one x).symm
  | succ n ih =>
      change (BitVec.ofNat 8 x).toNat + 256 * decodeLE (encodeLE n (x / 256)) =
        x % 256 ^ (n + 1)
      rw [ih]
      change x % 256 + 256 * ((x / 256) % 256 ^ n) = x % 256 ^ (n + 1)
      rw [pow_succ']
      exact (Nat.mod_mul (a := 256) (b := 256 ^ n) (x := x)).symm

/-- In particular, the existing Firedancer digest bitvector denotes the
little-endian integer assembled from its 64 output bytes. -/
@[simp] theorem decodeLE_bytesOf {n : Nat} (w : BitVec (n * 8)) :
    decodeLE (bytesOf w) = w.toNat := by
  rw [bytesOf_eq_encodeLE, decodeLE_encodeLE, radix_pow,
    Nat.mod_eq_of_lt w.isLt]

theorem decodeLE_lt (bs : Bytes) : decodeLE bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [decodeLE]
  | cons b bs ih =>
      have hb : b.toNat < 256 := b.isLt
      simp only [decodeLE, List.length_cons, pow_succ]
      omega

/-- Appending bytes adds them above the entire lower byte string. -/
theorem decodeLE_append (xs ys : Bytes) :
    decodeLE (xs ++ ys) = decodeLE xs + 256 ^ xs.length * decodeLE ys := by
  induction xs with
  | nil => simp [decodeLE]
  | cons b bs ih =>
      simp only [List.cons_append, decodeLE, List.length_cons, ih, pow_succ]
      ring

end Agave.Ed25519.Bridge.Challenge

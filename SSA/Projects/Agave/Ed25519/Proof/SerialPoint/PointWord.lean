import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.Word
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.Refinement

namespace Agave.Ed25519.SerialPoint
open SerialFieldMul

abbrev FieldWords := Fin 5 → BitVec 64

def addWord (a b : FieldWords) : FieldWords := fun i => a i + b i

def biasedSubWord (a b : FieldWords) : FieldWords :=
  fun i => a i + (bias i : BitVec 64) - b i

def subWord (a b : FieldWords) : FieldWords := weakWord (biasedSubWord a b)

theorem addWord_unsigned (a b : FieldWords)
    (ha : Bounded (unsigned a)) (hb : Bounded (unsigned b)) :
    unsigned (addWord a b) = add (unsigned a) (unsigned b) := by
  funext i
  have hA := ha i
  have hB := hb i
  change (a i).toNat < 2^54 at hA
  change (b i).toNat < 2^54 at hB
  simp only [unsigned, addWord, add, BitVec.toNat_add]
  apply Nat.mod_eq_of_lt
  omega

/-- The bias prevents natural subtraction underflow, and the caller bound
keeps the intermediate addition below 2^64. -/
theorem biasedSubWord_unsigned (a b : FieldWords)
    (ha : Bounded (unsigned a)) (hb : Bounded (unsigned b)) :
    unsigned (biasedSubWord a b) = biasedSub (unsigned a) (unsigned b) := by
  have hs := sub_safe (unsigned a) (unsigned b) ha hb
  funext i
  have hc : biasedSubWord a b i =
      ((biasedSub (unsigned a) (unsigned b) i : Nat) : BitVec 64) := by
    simp only [biasedSubWord, biasedSub, Nat.cast_sub (hs.2.1 i), Nat.cast_add]
    simp only [unsigned, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  change (biasedSubWord a b i).toNat = _
  rw [hc, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  exact lt_of_le_of_lt (Nat.sub_le _ _) (hs.1 i)

theorem subWord_unsigned (a b : FieldWords)
    (ha : Bounded (unsigned a)) (hb : Bounded (unsigned b)) :
    unsigned (subWord a b) = sub (unsigned a) (unsigned b) := by
  rw [subWord, weakWord_unsigned, biasedSubWord_unsigned a b ha hb]
  rfl

end Agave.Ed25519.SerialPoint

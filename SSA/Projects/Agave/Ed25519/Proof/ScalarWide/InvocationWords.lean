import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InvocationCalls
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputSplitArithmetic
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.WrapperModularSum
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Serialization

/-! Complete byte-level result of the instantiated two Montgomery calls and
modular addition; all constants and both input splits are concrete. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
open Agave.Ed25519.Bridge
open Subtraction

def lowWords (g : Globals) (state : GlobalState) (bytes : BitVec 512) : Fin 5 → BitVec 64 :=
  ScalarMontgomeryMul.tailWords
    (ScalarMontgomeryMul.quotient52 (lowSplitWords bytes) rWords (slot state 10) g.address0)

def highWords (g : Globals) (state : GlobalState) (bytes : BitVec 512) : Fin 5 → BitVec 64 :=
  ScalarMontgomeryMul.tailWords
    (ScalarMontgomeryMul.quotient52 (highSplitWords bytes) rrWords (slot state 9) g.address1)

def finalWords (g : Globals) (state : GlobalState) (bytes : BitVec 512) : Fin 5 → BitVec 64 :=
  ScalarMontgomeryMul.tailWords (sum52 (lowWords g state bytes) (highWords g state bytes))

theorem tailWords_bound (x : Fin 5 → BitVec 52) (i : Fin 5) :
    (ScalarMontgomeryMul.tailWords x i).toNat < 2 ^ 52 := by
  fin_cases i <;> change (_ &&& 4503599627370495#64).toNat < 2 ^ 52 <;>
    rw [ScalarMontgomeryMul.mask52_toNat] <;> exact Nat.mod_lt _ (by decide)

theorem lowWords_correct (g : Globals) (state : GlobalState) (bytes : BitVec 512) :
    ScalarMontgomeryMul.limbValue (fun i => (lowWords g state bytes i).toNat) =
        (bytes.toNat % 2 ^ 260) % subgroupOrder ∧
      ScalarMontgomeryMul.limbValue (fun i => (lowWords g state bytes i).toNat) < subgroupOrder := by
  have h := ScalarMontgomeryMul.montgomery_words_correct (lowSplitWords bytes) rWords
    (slot state 10) g.address0 1 (lowSplitWords_bound bytes) rWords_bound
    rWords_canonical rWords_factor
  simpa only [lowWords, lowSplitWords_value, Nat.mul_one] using h

theorem highWords_correct (g : Globals) (state : GlobalState) (bytes : BitVec 512) :
    ScalarMontgomeryMul.limbValue (fun i => (highWords g state bytes i).toNat) =
        ((bytes.toNat / 2 ^ 260) * 2 ^ 260) % subgroupOrder ∧
      ScalarMontgomeryMul.limbValue (fun i => (highWords g state bytes i).toNat) < subgroupOrder := by
  have h := ScalarMontgomeryMul.montgomery_words_correct (highSplitWords bytes) rrWords
    (slot state 9) g.address1 (2 ^ 260) (highSplitWords_bound bytes) rrWords_bound
    rrWords_canonical rrWords_factor
  simpa only [highWords, highSplitWords_value] using h

theorem finalWords_correct (g : Globals) (state : GlobalState) (bytes : BitVec 512) :
    ScalarMontgomeryMul.limbValue (fun i => (finalWords g state bytes i).toNat) =
      bytes.toNat % subgroupOrder := by
  have hlo := lowWords_correct g state bytes
  have hhi := highWords_correct g state bytes
  have h := wrapper_modular_sum (lowWords g state bytes) (highWords g state bytes)
    (tailWords_bound _) (tailWords_bound _) hlo.2 hhi.2
  rw [hlo.1, hhi.1, ← Nat.add_mod] at h
  have he : bytes.toNat % 2 ^ 260 + bytes.toNat / 2 ^ 260 * 2 ^ 260 = bytes.toNat := by
    simpa only [Nat.mul_comm] using Nat.mod_add_div bytes.toNat (2 ^ 260)
  simpa only [finalWords, he] using h

def finalPacked (g : Globals) (state : GlobalState) (bytes : BitVec 512) : BitVec 256 :=
  (packedOutput (finalWords g state bytes)).setWidth 256

theorem finalPacked_eq (g : Globals) (state : GlobalState) (bytes : BitVec 512) :
    finalPacked g state bytes = Challenge.reducedBytes bytes := by
  have hb : ∀ i, (finalWords g state bytes i).toNat < 2 ^ 52 := tailWords_bound _
  have hv := finalWords_correct g state bytes
  have hp : (packedOutput (finalWords g state bytes)).toNat = bytes.toNat % subgroupOrder := by
    simpa only [packedOutput, packed_toNat, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (hb _), ScalarMontgomeryMul.limbValue] using hv
  have hsmall : bytes.toNat % subgroupOrder < 2 ^ 256 :=
    (Nat.mod_lt _ (by decide : 0 < subgroupOrder)).trans (by decide)
  apply BitVec.eq_of_toNat_eq
  rw [finalPacked, BitVec.toNat_setWidth, hp, Nat.mod_eq_of_lt hsmall, Challenge.reducedBytes_toNat]
  rfl

theorem finalSerializedBytes_eq (g : Globals) (state : GlobalState) (bytes : BitVec 512)
    (i : Fin 32) :
    serializedBytes (finalWords g state bytes) i =
      (Challenge.reducedBytes bytes).extractLsb' (8 * i.val) 8 := by
  let x : Fin 5 → BitVec 52 := fun j => (finalWords g state bytes j).setWidth 52
  have hw (j : Fin 5) : (x j).setWidth 64 = finalWords g state bytes j := by
    apply BitVec.eq_of_toNat_eq
    simp only [x, BitVec.toNat_setWidth_of_le (by decide : 52 ≤ 64),
      BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (tailWords_bound _ j)
  have he : (fun j => (x j).setWidth 64) = finalWords g state bytes := funext hw
  rw [← he, serializedBytes_packed]
  change (finalPacked g state bytes).extractLsb' (8 * i.val) 8 = _
  rw [finalPacked_eq]

end Agave.Ed25519.Verifier.Execution.ScalarWide

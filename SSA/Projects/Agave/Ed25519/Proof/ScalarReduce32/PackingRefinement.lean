import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.MachineCertificate
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Subtract
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PackingWords
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PackPhase
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.StorePhase
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Output
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Serialization

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Arithmetic
open Agave.Ed25519.Bridge
open Agave.Ed25519.Verifier.Execution
open ScalarMontgomeryMul
open ScalarWide.Subtraction
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The subtraction output is the canonical remainder for every 256-bit input. -/
theorem reductionWords_correct (bits : BitVec 256) :
    limbValue (fun i => (subtractWords (reductionQuotient (inputWords bits)) i).toNat) =
      bits.toNat % subgroupOrder ∧
    limbValue (fun i => (subtractWords (reductionQuotient (inputWords bits)) i).toNat) <
      subgroupOrder := by
  have hwords := tailWords_value (reductionQuotient (inputWords bits))
  change limbValue (fun i => (subtractWords (reductionQuotient (inputWords bits)) i).toNat) =
    finish (rawValue (reductionQuotient (inputWords bits))) at hwords
  rw [hwords]
  exact reduction_finish_correct bits



/-- Canonical bytes of the complete source word computation. -/
theorem reductionBytes_correct (bits : BitVec 256) :
    reductionBytes (reductionPackingWords (reductionQuotient (inputWords bits))) =
      fun i => (Dalek.reduceScalarBytes bits).extractLsb' (8 * i.val) 8 := by
  let q := reductionQuotient (inputWords bits)
  have hm : packedOutput (reductionPackingWords q) = packedOutput (subtractWords q) := by
    rw [← packedOutput_mask]
    congr 1
    funext i
    exact reductionPackingWords_mask q i
  have hn := (reductionWords_correct bits).1
  have hword (i : Fin 5) : (subtractWords q i).toNat < 2 ^ 52 := by
    rw [subtractWords, ← reductionPackingWords_mask q i, mask52_toNat]
    exact Nat.mod_lt _ (by decide)
  have hp : (packedOutput (subtractWords q)).toNat = bits.toNat % subgroupOrder := by
    simp only [packedOutput, packed_toNat, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (hword _)]
    exact hn
  have he : (packedOutput (subtractWords q)).setWidth 256 = Dalek.reduceScalarBytes bits := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, hp, Dalek.reduceScalarBytes, BitVec.toNat_ofNat]
    rfl
  funext i
  rw [reductionBytes_packed, hm, he]

end Agave.Ed25519.ScalarReduce32.Execution

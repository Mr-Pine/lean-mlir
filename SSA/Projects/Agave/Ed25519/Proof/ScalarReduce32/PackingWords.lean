import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.ProductRefinement
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PackPhase
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.StorePhase
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

/-- The unmasked words consumed by the actual byte-packing instructions. -/
def reductionPackingWords (x : Fin 5 → BitVec 52) : Fin 5 → BitVec 64 :=
  let d := differences (x 0) (x 1) (x 2) (x 3) (x 4)
  let mask := (0 : BitVec 64) - (borrowByte d).setWidth 64
  let t0 := (d 0 &&& 4503599627370495#64) + (mask &&& 671914833335277#64)
  let t1 := (t0 >>> 52) + (mask &&& 3916664325105025#64) +
    (d 1 &&& 4503599627370495#64)
  let t2 := (d 2 &&& 4503599627370495#64) + (mask &&& 1367801#64) + (t1 >>> 52)
  let t3 := (t2 >>> 52) + (d 3 &&& 4503599627370495#64)
  let t4 := d 4 + (mask &&& 17592186044416#64) + (t3 >>> 52)
  ![t0, t1, t2, t3, t4]

theorem reductionPackingWords_mask (x : Fin 5 → BitVec 52) (i : Fin 5) :
    reductionPackingWords x i &&& 4503599627370495#64 = addback (differences (x 0) (x 1) (x 2) (x 3) (x 4)) i := by
  fin_cases i <;> rfl

theorem reductionPackingWords_bound (x : Fin 5 → BitVec 52) :
    (reductionPackingWords x 3).toNat < 2 ^ 53 := by
  let d := differences (x 0) (x 1) (x 2) (x 3) (x 4)
  let t2 := reductionPackingWords x 2
  have hd : (d 3 &&& 4503599627370495#64).toNat < 2 ^ 52 := by
    rw [mask52_toNat]
    exact Nat.mod_lt _ (by decide)
  have ht := t2.isLt
  change (((t2 >>> 52) + (d 3 &&& 4503599627370495#64))).toNat < _
  rw [BitVec.toNat_add]
  apply (Nat.mod_le _ _).trans_lt
  simp only [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.reduceMod, Nat.shiftRight_eq_div_pow]
  norm_num at hd ht ⊢
  omega

/-- Exact bytes in registers 351 through 415. -/
def reductionBytes (words : Fin 5 → BitVec 64) : Bytes :=
  ![(words 0).setWidth 8,
    ((words 0) >>> 8).setWidth 8,
    ((words 0) >>> 16).setWidth 8,
    ((words 0) >>> 24).setWidth 8,
    ((words 0) >>> 32).setWidth 8,
    ((words 0) >>> 40).setWidth 8,
    ((((words 1) &&& 4503599627370495#64) <<< 4) ||| (((words 0) &&& 4503599627370495#64) >>> 48)).setWidth 8,
    ((words 1) >>> 4).setWidth 8,
    ((words 1) >>> 12).setWidth 8,
    ((words 1) >>> 20).setWidth 8,
    ((words 1) >>> 28).setWidth 8,
    ((words 1) >>> 36).setWidth 8,
    ((words 1) >>> 44).setWidth 8,
    (words 2).setWidth 8,
    ((words 2) >>> 8).setWidth 8,
    ((words 2) >>> 16).setWidth 8,
    ((words 2) >>> 24).setWidth 8,
    ((words 2) >>> 32).setWidth 8,
    ((words 2) >>> 40).setWidth 8,
    (((words 3) <<< 4) ||| (((words 2) &&& 4503599627370495#64) >>> 48)).setWidth 8,
    ((words 3) >>> 4).setWidth 8,
    ((words 3) >>> 12).setWidth 8,
    ((words 3) >>> 20).setWidth 8,
    ((words 3) >>> 28).setWidth 8,
    ((words 3) >>> 36).setWidth 8,
    ((words 3) >>> 44).setWidth 8,
    (words 4).setWidth 8,
    ((words 4) >>> 8).setWidth 8,
    ((words 4) >>> 16).setWidth 8,
    ((words 4) >>> 24).setWidth 8,
    ((words 4) >>> 32).setWidth 8,
    ((words 4) >>> 40).setWidth 8]

/-- Masking the radix limbs loses no serialized bits, including byte boundaries. -/
theorem reductionBytes_packed (words : Fin 5 → BitVec 64) (byte : Fin 32) :
    reductionBytes words byte =
      ((packedOutput words).setWidth 256).extractLsb' (8 * byte.val) 8 := by
  fin_cases byte <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  all_goals interval_cases i <;>
    simp [reductionBytes, packedOutput, packed, BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_or, BitVec.getLsbD_and, input_mask_bits, BitVec.getLsbD_append,
      BitVec.getElem_append]
  all_goals repeat (rw [BitVec.getElem_append]; norm_num)

theorem packedOutput_mask (words : Fin 5 → BitVec 64) :
    packedOutput (fun i => words i &&& 4503599627370495#64) = packedOutput words := by
  have hm (word : BitVec 64) : (word &&& 4503599627370495#64).setWidth 52 =
      word.setWidth 52 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, mask52_toNat, Nat.mod_mod]
  simp only [packedOutput, hm]

end Agave.Ed25519.ScalarReduce32.Execution

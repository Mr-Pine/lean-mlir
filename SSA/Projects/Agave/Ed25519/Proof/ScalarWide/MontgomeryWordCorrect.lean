import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.ProductRefinement
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.UpperRefinement
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryTail

/-! End-to-end arithmetic of the exact source word expressions. This is not yet
a complete memory execution theorem: it supplies the numeric refinement and
normalized register values for the separately proved machine phases. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open LeanMLIR.RIR
open Agave.Ed25519.Bridge
open Agave.Ed25519.ScalarReduce32.Arithmetic
open ScalarWide.Subtraction

/-- Normalized view of the five actual quotient words. -/
def quotient52 (a b : Fin 5 → BitVec 64) (left right : Pointer) : Fin 5 → BitVec 52 :=
  fun i => (wordQuotientLimbs (columnWords a b left right) i).setWidth 52

/-- The actual word quotient equals the certified natural quotient, limb by limb. -/
theorem actual_quotient_toNat (a b : Fin 5 → BitVec 64) (left right : Pointer)
    (ha : ∀ i, (a i).toNat < 2 ^ 52) (hb : ∀ i, (b i).toNat < 2 ^ 52)
    (hcanonical : limbValue (fun i => (b i).toNat) < subgroupOrder) :
    ∀ i, (wordQuotientLimbs (columnWords a b left right) i).toNat =
      quotientLimbs (productColumns (fun j => (a j).toNat) (fun j => (b j).toNat)) i := by
  have hinput : limbValue (fun i => (a i).toNat) < 2 ^ 260 :=
    adjustment_bound _ _ _ _ _ (ha 0) (ha 1) (ha 2) (ha 3) (ha 4)
  have he : (fun i => (columnWords a b left right i).toNat) =
      productColumns (fun i => (a i).toNat) (fun i => (b i).toNat) := by
    funext i
    exact columnWords_toNat a b left right ha hb i
  have htop := (quotientLimbs_bounds _ _ hinput hcanonical).2
  intro i
  have h := wordQuotientLimbs_toNat (columnWords a b left right)
    (columnWords_bound a b left right ha hb) (by rw [he]; exact htop.trans (by decide)) i
  simpa only [he] using h

/-- No quotient bits are lost when establishing the tail's normalized inputs. -/
theorem quotient52_widen (a b : Fin 5 → BitVec 64) (left right : Pointer)
    (ha : ∀ i, (a i).toNat < 2 ^ 52) (hb : ∀ i, (b i).toNat < 2 ^ 52)
    (hcanonical : limbValue (fun i => (b i).toNat) < subgroupOrder) (i : Fin 5) :
    (quotient52 a b left right i).setWidth 64 =
      wordQuotientLimbs (columnWords a b left right) i := by
  have hinput : limbValue (fun i => (a i).toNat) < 2 ^ 260 :=
    adjustment_bound _ _ _ _ _ (ha 0) (ha 1) (ha 2) (ha 3) (ha 4)
  have hnat := actual_quotient_toNat a b left right ha hb hcanonical i
  have hbound := (quotientLimbs_bounds _ _ hinput hcanonical).1 i
  apply BitVec.eq_of_toNat_eq
  simp only [quotient52, BitVec.toNat_setWidth_of_le (by decide : 52 ≤ 64),
    BitVec.toNat_setWidth, hnat, Nat.mod_eq_of_lt hbound]

/-- The five normalized quotient inputs denote exactly the certified quotient. -/
theorem quotient52_value (a b : Fin 5 → BitVec 64) (left right : Pointer)
    (ha : ∀ i, (a i).toNat < 2 ^ 52) (hb : ∀ i, (b i).toNat < 2 ^ 52)
    (hcanonical : limbValue (fun i => (b i).toNat) < subgroupOrder) :
    rawValue (quotient52 a b left right) =
      (productSchedule (fun i => (a i).toNat) (fun i => (b i).toNat)).2 := by
  have hinput : limbValue (fun i => (a i).toNat) < 2 ^ 260 :=
    adjustment_bound _ _ _ _ _ (ha 0) (ha 1) (ha 2) (ha 3) (ha 4)
  have hbounds := (quotientLimbs_bounds _ _ hinput hcanonical).1
  have hnat := actual_quotient_toNat a b left right ha hb hcanonical
  have hi (i : Fin 5) : (quotient52 a b left right i).toNat =
      quotientLimbs (productColumns (fun j => (a j).toNat) (fun j => (b j).toNat)) i := by
    rw [quotient52, BitVec.toNat_setWidth, hnat i, Nat.mod_eq_of_lt (hbounds i)]
  simp only [rawValue, hi]
  exact quotientLimbs_value (productColumns (fun i => (a i).toNat) (fun i => (b i).toNat))

/-- Complete source-word Montgomery reduction, applicable to literal R or RR. -/
theorem montgomery_words_correct (a b : Fin 5 → BitVec 64) (left right : Pointer)
    (factor : Nat) (ha : ∀ i, (a i).toNat < 2 ^ 52) (hb : ∀ i, (b i).toNat < 2 ^ 52)
    (hcanonical : limbValue (fun i => (b i).toNat) < subgroupOrder)
    (hconstant : limbValue (fun i => (b i).toNat) % subgroupOrder =
      (factor * 2 ^ 260) % subgroupOrder) :
    limbValue (fun i => (tailWords (quotient52 a b left right) i).toNat) =
        (limbValue (fun i => (a i).toNat) * factor) % subgroupOrder ∧
      limbValue (fun i => (tailWords (quotient52 a b left right) i).toNat) < subgroupOrder := by
  have hinput : limbValue (fun i => (a i).toNat) < 2 ^ 260 :=
    adjustment_bound _ _ _ _ _ (ha 0) (ha 1) (ha 2) (ha 3) (ha 4)
  have hwords := tailWords_value (quotient52 a b left right)
  rw [quotient52_value a b left right ha hb hcanonical] at hwords
  change limbValue (fun i => (tailWords (quotient52 a b left right) i).toNat) =
    finish (productSchedule (fun i => (a i).toNat) (fun i => (b i).toNat)).2 at hwords
  rw [hwords]
  exact productSchedule_correct _ _ factor hinput hcanonical hconstant

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

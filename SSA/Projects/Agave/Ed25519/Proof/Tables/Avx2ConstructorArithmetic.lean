import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCacheArithmetic
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointDouble.MixingPacking
import SSA.Projects.Agave.Ed25519.Proof.Tables.Dynamic
import SSA.Projects.Firedancer.Prime
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhasePipeline

/-! The concrete limb recurrence used by the seven actual AVX2 iterations. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Arithmetic
open Avx2PointAdd Avx2PointAdd.Phases Avx2PointDouble PointArithmetic CacheArithmetic
local instance : Fact (Nat.Prime Field.p) := ⟨prime_p⟩

def entries (P : Point) : Nat → Point
  | 0 => cache P
  | n+1 => cache (add (doublePoint P) (entries P n))

theorem entries_reduced {P : Point} (hP : pointReduced P) (n : Nat) :
    pointReduced (entries P n) := by
  induction n with
  | zero => exact cache_reduced hP
  | succ n ih => exact cache_reduced (add_reduced (doublePoint_reduced hP) (pointReduced_wide ih))

theorem entries_value {P : Point} (hP : pointReduced P) (n : Nat) :
    pointValue (entries P n) = avx2Cache (avx2Odd (pointValue P) n) := by
  induction n with
  | zero => exact cache_value hP
  | succ n ih =>
    have hc := entries_reduced hP n
    rw [entries, cache_value (add_reduced (doublePoint_reduced hP) (pointReduced_wide hc)),
      add_refines (doublePoint_reduced hP) (pointReduced_wide hc), doublePoint_value hP, ih]
    rfl

theorem width5 {P : Point} (hP : pointReduced P) (k : Fin 8) :
    pointReduced (entries P k.val) ∧
      pointValue (entries P k.val) = avx2Cache (avx2Width5 (pointValue P) k) :=
  ⟨entries_reduced hP k.val, entries_value hP k.val⟩

end Agave.Ed25519.Tables.Avx2Constructor.Arithmetic

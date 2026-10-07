import SSA.Projects.Agave.Ed25519.Proof.Tables.Static
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.Refinement

namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open Tables (F avx2BaseWord avx2BaseCoordinate avx2BaseCache avx2BasePoint)
open Avx2PointAdd (Point pointReduced pointValue)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- The physical even/odd words of one coordinate in the immutable SIMD table. -/
def baseCacheLimbs (k : Fin 64) (lo hi : Fin 8) : Avx2FieldMul.Limbs :=
  ![avx2BaseWord k 0 lo, avx2BaseWord k 0 hi,
    avx2BaseWord k 1 lo, avx2BaseWord k 1 hi,
    avx2BaseWord k 2 lo, avx2BaseWord k 2 hi,
    avx2BaseWord k 3 lo, avx2BaseWord k 3 hi,
    avx2BaseWord k 4 lo, avx2BaseWord k 4 hi]

def baseCachePoint (k : Fin 64) : Point :=
  ⟨baseCacheLimbs k 0 2, baseCacheLimbs k 1 3,
    baseCacheLimbs k 4 6, baseCacheLimbs k 5 7⟩

/-- A closed kernel certificate checks every stored word of all 64 records. -/
theorem baseCachePoint_reduced (k : Fin 64) : pointReduced (baseCachePoint k) := by
  unfold pointReduced baseCachePoint Avx2PointAdd.reduced
  fin_cases k <;> decide +kernel

theorem baseCacheLimbs_value_core (u : Fin 5 → Fin 8 → Nat) (lo hi : Fin 8) :
    Avx2PointAdd.value ![u 0 lo, u 0 hi, u 1 lo, u 1 hi, u 2 lo, u 2 hi,
      u 3 lo, u 3 hi, u 4 lo, u 4 hi] =
      ∑ i : Fin 5, ((u i lo : F) + 2^26 * u i hi) * 2^(51 * i.val) := by
  norm_num [Avx2PointAdd.value, Field.decode10, Field.exponent, Fin.sum_univ_succ]
  ring

theorem baseCacheLimbs_value (k : Fin 64) (lo hi : Fin 8) :
    Avx2PointAdd.value (baseCacheLimbs k lo hi) = avx2BaseCoordinate k lo hi :=
  baseCacheLimbs_value_core (avx2BaseWord k) lo hi

theorem baseCachePoint_value (k : Fin 64) :
    pointValue (baseCachePoint k) = PointArithmetic.avx2Cache (avx2BasePoint k) := by
  rw [← Tables.avx2BaseCache_correct k]
  simp only [pointValue, baseCachePoint, avx2BaseCache, baseCacheLimbs_value]

end Agave.Ed25519.DoubleBase.ExecutionAvx2

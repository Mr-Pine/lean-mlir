import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.Word
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.Refinement

namespace Agave.Ed25519.SerialPoint
open SerialFieldMul
section

/-- Bitvector expression from the actual inlined `pow2k(1)` columns. -/
def squareWordColumns (a : Fin 5 → BitVec 64) : Fin 5 → BitVec 128 :=
  let A := fun i => (a i).setWidth 128
  let A19 := fun i => (a i * 19).setWidth 128
  ![((A 1*A19 4 + A 2*A19 3) <<< 1#128) + A 0*A 0,
    ((A 0*A 1 + A 2*A19 4) <<< 1#128) + A19 3*A 3,
    ((A 0*A 2 + A19 3*A 4) <<< 1#128) + A 1*A 1,
    ((A 0*A 3 + A 1*A 2) <<< 1#128) + A19 4*A 4,
    ((A 0*A 4 + A 1*A 3) <<< 1#128) + A 2*A 2]

def squareMachine (a : Fin 5 → BitVec 64) : Fin 5 → BitVec 64 :=
  wordSchedule (squareWordColumns a)

theorem shl_one (x : BitVec 128) : x <<< 1#128 = x*2 := by
  change x <<< (1 : Nat) = x * 2
  exact BitVec.shiftLeft_eq_mul_twoPow x 1

theorem squareWordColumns_eq (a : Fin 5 → BitVec 64) (ha : Bounded (unsigned a)) :
    squareWordColumns a = fun i => (squareColumns (unsigned a) i : BitVec 128) := by
  have hs (i : Fin 5) : (a i * 19).setWidth 128 =
      ((unsigned a i * 19 : Nat) : BitVec 128) := widen_scale_eq_cast _ (ha i)
  have htwo : BitVec.twoPow 128 1 = 2#128 := rfl
  funext i
  fin_cases i <;> simp only [squareWordColumns, hs] <;>
    simp [squareColumns, widen_eq_cast, BitVec.shiftLeft_eq_mul_twoPow, htwo,
      unsigned, Nat.cast_add, Nat.cast_mul,
      -BitVec.mul_twoPow_eq_shiftLeft, -BitVec.natCast_eq_ofNat,
      -BitVec.ofNat_toNat] <;> ring

theorem squareMachine_eq (a : Fin 5 → BitVec 64) (ha : Bounded (unsigned a)) :
    squareMachine a = fun i => (sq (unsigned a) i : BitVec 64) := by
  unfold squareMachine sq
  rw [squareWordColumns_eq a ha, squareColumns_eq]
  exact wordSchedule_eq _ (carried_bounds _ _ ha ha).1 (carried_bounds _ _ ha ha).2

theorem squareMachine_eq_mul (a : Fin 5 → BitVec 64) (ha : Bounded (unsigned a)) :
    squareMachine a = machine a a := by
  rw [squareMachine_eq a ha, machine_eq_reduce a a ha ha]
  simp only [sq, squareColumns_eq]

/-- The carry schedule returns the exact natural limbs, including its final
64-bit casts, under the serial field caller's 54-bit input bound. -/
theorem squareMachine_unsigned (a : Fin 5 → BitVec 64) (ha : Bounded (unsigned a)) :
    unsigned (squareMachine a) = sq (unsigned a) := by
  rw [squareMachine_eq_mul a ha, machine_unsigned a a ha ha]
  simp only [sq, squareColumns_eq]

theorem squareMachine_tight (a : Fin 5 → BitVec 64) (ha : Bounded (unsigned a)) :
    Tight (unsigned (squareMachine a)) := by
  rw [squareMachine_unsigned a ha]
  exact sq_tight _ ha

/-- Field refinement of the inlined serial square word schedule. -/
theorem squareMachine_value (a : Fin 5 → BitVec 64) (ha : Bounded (unsigned a)) :
    value (unsigned (squareMachine a)) = value (unsigned a) ^ 2 := by
  rw [squareMachine_unsigned a ha]
  exact square_value _

end
end Agave.Ed25519.SerialPoint

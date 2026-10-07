import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.WordRefinement

namespace Agave.Ed25519.SerialPoint.Execution
open SerialFieldMul

abbrev PointWords := Fin 20 → BitVec 64

/-- Four consecutive five-limb coordinates in physical Edwards order. -/
def pointFromWords (p : PointWords) : WordPoint :=
  ⟨![p 0, p 1, p 2, p 3, p 4], ![p 5, p 6, p 7, p 8, p 9],
   ![p 10, p 11, p 12, p 13, p 14], ![p 15, p 16, p 17, p 18, p 19]⟩

/-- ProjectiveNiels memory stores Y+X before Y-X; the formula uses the reverse. -/
def cacheFromWords (c : PointWords) : WordPoint :=
  let p := pointFromWords c
  ⟨p.Y, p.X, p.Z, p.T⟩

def pointToWords (p : WordPoint) : PointWords :=
  ![p.X 0, p.X 1, p.X 2, p.X 3, p.X 4,
    p.Y 0, p.Y 1, p.Y 2, p.Y 3, p.Y 4,
    p.Z 0, p.Z 1, p.Z 2, p.Z 3, p.Z 4,
    p.T 0, p.T 1, p.T 2, p.T 3, p.T 4]

@[simp] theorem pointFromWords_toWords (p : WordPoint) :
    pointFromWords (pointToWords p) = p := by
  apply PointArithmetic.Extended.ext <;> funext i <;> fin_cases i <;> rfl

end Agave.Ed25519.SerialPoint.Execution

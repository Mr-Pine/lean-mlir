
namespace LimbRepresentations

abbrev Limbs (limbWidth vecLength : Nat) := Vector (BitVec limbWidth) vecLength

def placeValues (vecLength baseBits: Nat) := (Vector.range vecLength).map (λ i => (2: Int)^(i*baseBits))
def decode (limbWidth baseBits vecLength: Nat) (limbs: Limbs limbWidth vecLength) :=
  let limbValues := limbs.map (BitVec.toInt)
  ((placeValues vecLength baseBits).zipWith (.*.) limbValues).sum

end LimbRepresentations

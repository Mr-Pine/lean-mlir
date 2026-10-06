import SSA.Projects.Agave.Ed25519.Proof.ReduceBitcast
import SSA.Projects.RIR.Run.Vector

/-! The square kernel's two unpack shuffles select only defined zero lanes
from the compiler's partially-poison constants. -/

namespace Agave.Ed25519.Avx2SquareNegateD
open LeanMLIR.RIR
section

def evenZeros : ⟦Ty.vec 8 32⟧ :=
  #v[.value 0, .value 0, .poison, .poison, .value 0, .value 0, .poison, .poison]

def oddZeros : ⟦Ty.vec 8 32⟧ :=
  #v[.poison, .poison, .value 0, .value 0, .poison, .poison, .value 0, .value 0]

def evenMask : Vector (Option (Fin 16)) 8 :=
  #v[some 0, some 8, some 1, some 9, some 4, some 12, some 5, some 13]

def oddMask : Vector (Option (Fin 16)) 8 :=
  #v[some 2, some 10, some 3, some 11, some 6, some 14, some 7, some 15]

def evenInterleave (x : V32) : V32 := #v[x[0], 0, x[1], 0, x[4], 0, x[5], 0]
def oddInterleave (x : V32) : V32 := #v[x[2], 0, x[3], 0, x[6], 0, x[7], 0]

def unpackEven (x : V32) : V64 :=
  #v[x[0].setWidth 64, x[1].setWidth 64, x[4].setWidth 64, x[5].setWidth 64]
def unpackOdd (x : V32) : V64 :=
  #v[x[2].setWidth 64, x[3].setWidth 64, x[6].setWidth 64, x[7].setWidth 64]

theorem even_shuffle (x : V32) :
    Operation.shufflevector evenMask (Ty.wrap x) evenZeros = Ty.wrap (evenInterleave x) := by
  apply Vector.ext
  intro i hi
  obtain _|_|_|_|_|_|_|_|i := i
  all_goals try omega
  all_goals simp [Operation.shufflevector, evenMask, Ty.wrap_vec, evenZeros, evenInterleave]

theorem odd_shuffle (x : V32) :
    Operation.shufflevector oddMask (Ty.wrap x) oddZeros = Ty.wrap (oddInterleave x) := by
  apply Vector.ext
  intro i hi
  obtain _|_|_|_|_|_|_|_|i := i
  all_goals try omega
  all_goals simp [Operation.shufflevector, oddMask, Ty.wrap_vec, oddZeros, oddInterleave]

theorem zero_append_eq_wide (x : BitVec 32) : 0#32 ++ x = x.setWidth 64 := by
  simpa using (BitVec.setWidth_eq_append (x := x) (w := 64) (by decide)).symm

theorem even_interleave_join (x : V32) : join64 (evenInterleave x) = unpackEven x := by
  apply Vector.ext
  intro i hi
  obtain _|_|_|_|i := i
  all_goals try omega
  all_goals simp [join64, evenInterleave, unpackEven, zero_append_eq_wide]

theorem odd_interleave_join (x : V32) : join64 (oddInterleave x) = unpackOdd x := by
  apply Vector.ext
  intro i hi
  obtain _|_|_|_|i := i
  all_goals try omega
  all_goals simp [join64, oddInterleave, unpackOdd, zero_append_eq_wide]

/-- Exact RIR instruction semantics for unpacking the four even limbs. -/
theorem unpack_even_instructions (x : V32) :
    Operation.bitcast (t := .vec 8 32) (t' := .vec 4 64) (by decide)
      (Operation.shufflevector evenMask (Ty.wrap x) evenZeros) = Ty.wrap (unpackEven x) := by
  rw [even_shuffle]
  erw [bitcast_join64]
  rw [even_interleave_join]

/-- Exact RIR instruction semantics for unpacking the four odd limbs. -/
theorem unpack_odd_instructions (x : V32) :
    Operation.bitcast (t := .vec 8 32) (t' := .vec 4 64) (by decide)
      (Operation.shufflevector oddMask (Ty.wrap x) oddZeros) = Ty.wrap (unpackOdd x) := by
  rw [odd_shuffle]
  erw [bitcast_join64]
  rw [odd_interleave_join]

end
end Agave.Ed25519.Avx2SquareNegateD

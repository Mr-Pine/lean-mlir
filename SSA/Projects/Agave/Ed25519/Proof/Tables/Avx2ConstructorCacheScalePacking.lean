import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCacheScaleVectors

namespace Agave.Ed25519.Tables.Avx2Constructor.CacheScale
open LeanMLIR.RIR Avx2PointAdd Avx2PointAdd.Phases Avx2SquareNegateD
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] Ty.width

def lowMask (n : Nat) : ⟦Ty.vec 8 32⟧ :=
  #v[.value (BitVec.ofNat 32 n), .poison, .value (BitVec.ofNat 32 n), .poison,
     .value (BitVec.ofNat 32 n), .poison, .value (BitVec.ofNat 32 n), .poison]

def pairMask : Vector (Option (Fin 16)) 8 :=
  #v[some 0, some 2, some 8, some 10, some 4, some 6, some 12, some 14]

def packInstructions (z : Fin 10 → ⟦Ty.vec 4 64⟧) (k : Fin 5) : ⟦Ty.vec 8 32⟧ :=
  let even : ⟦Ty.vec 8 32⟧ := Operation.bitcast (by decide) (z (evenIndex k))
  let odd : ⟦Ty.vec 8 32⟧ := Operation.bitcast (by decide) (z (oddIndex k))
  let maskedEven := Vector.zipWith Operation.and even (lowMask 67108863)
  let maskedOdd := if k = 0 ∨ k = 2 then odd else
    Vector.zipWith Operation.and odd (lowMask 33554431)
  Operation.shufflevector pairMask maskedEven maskedOdd

def packNat (z : Fin 10 → Fin 4 → Nat) (k : Fin 5) : V32 :=
  let n := fun lane => finalMask (fun i => z i lane)
  #v[word (n 0 (evenIndex k)), word (n 1 (evenIndex k)),
     word (n 0 (oddIndex k)), word (n 1 (oddIndex k)),
     word (n 2 (evenIndex k)), word (n 3 (evenIndex k)),
     word (n 2 (oddIndex k)), word (n 3 (oddIndex k))]

theorem low_ofNat (n : Nat) : (BitVec.ofNat 64 n).extractLsb' 0 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb', Nat.mod_mod_of_dvd]

theorem word_mask26 (n : Nat) : word n &&& 67108863#32 = word (n % 2^26) := by
  change BitVec.ofNat 32 n &&& BitVec.ofNat 32 (2^26-1) = _
  rw [← BitVec.ofNat_and, Nat.and_two_pow_sub_one_eq_mod]
  rfl

theorem word_mask25 (n : Nat) : word n &&& 33554431#32 = word (n % 2^25) := by
  change BitVec.ofNat 32 n &&& BitVec.ofNat 32 (2^25-1) = _
  rw [← BitVec.ofNat_and, Nat.and_two_pow_sub_one_eq_mod]
  rfl

theorem packInstructions_nat (z : Fin 10 → Fin 4 → Nat) (k : Fin 5) :
    packInstructions (fun i => Ty.wrap (t := .vec 4 64) (wideVec (z i))) k =
      Ty.wrap (packNat z k) := by
  fin_cases k <;>
    simp only [packInstructions, bitcast_split32]
  all_goals apply Vector.ext
  all_goals intro lane hlane
  all_goals interval_cases lane <;>
    simp [Operation.shufflevector, Operation.and, pairMask, lowMask,
      packNat, wideVec, split32, Ty.wrap_vec, finalMask, evenIndex, oddIndex,
      low_ofNat]
  all_goals first | exact word_mask26 _ | exact word_mask25 _ | rfl

theorem packNat_scaled {P : Point} (hP : pointWide P) (k : Fin 5) :
    packNat (fun i lane => scalarNat (fun j => scaledColumns P j lane) i) k =
      packPoint (scaledPoint P) k := by
  have hr (lane : Fin 4) := scalarNat_reduce (fun j => scaledColumns P j lane)
    (fun j => scaledColumns_bound hP j lane)
  simp only [packNat, hr]
  fin_cases k <;> rfl

/-- All source packing operations refine coordinatewise scaling and reduction. -/
theorem instructions_point {P : Point} (hP : pointWide P) (k : Fin 5) :
    packInstructions (reductionInstructions
      (scaleInstructions (fun j => Ty.wrap (t := .vec 8 32) (packPoint P j)))) k =
        Ty.wrap (packPoint (scaledPoint P) k) := by
  have hs : scaleInstructions (fun j => Ty.wrap (t := .vec 8 32) (packPoint P j)) =
      fun i => Ty.wrap (t := .vec 4 64) (wideVec (scaledColumns P i)) := by
    funext i
    exact scaleInstructions_point hP i
  rw [hs]
  have hr : reductionInstructions (fun i => Ty.wrap (t := .vec 4 64)
      (wideVec (scaledColumns P i))) = fun i => Ty.wrap (t := .vec 4 64)
        (wideVec (fun lane => scalarNat (fun j => scaledColumns P j lane) i)) := by
    funext i
    exact reductionInstructions_nat _ (scaledColumns_bound hP) (scaledColumns_even P) i
  rw [hr, packInstructions_nat, packNat_scaled hP]

end Agave.Ed25519.Tables.Avx2Constructor.CacheScale

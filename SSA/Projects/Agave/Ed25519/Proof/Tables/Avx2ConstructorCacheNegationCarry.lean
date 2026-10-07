import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCacheNegationWords

namespace Agave.Ed25519.Tables.Avx2Constructor.CacheNegation
open LeanMLIR.RIR Avx2PointAdd Avx2SquareNegateD Normalization
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] Ty.width

def pair (lo hi : BitVec 32) : ⟦Ty.vec 8 32⟧ :=
  #v[.poison,.poison,.poison,.poison,.poison,.value lo,.poison,.value hi]

def maskD : ⟦Ty.vec 8 32⟧ :=
  #v[.poison,.poison,.poison,.poison,.poison,.value 67108863#32,.poison,.value 33554431#32]

def firstInstructions (x : ⟦Ty.vec 8 32⟧) : ⟦Ty.vec 8 32⟧ :=
  let a := Vector.zipWith (Operation.lshr false) x (Ty.wrap (t := .vec 8 32) shifts)
  let b := Operation.shufflevector #v[none,none,none,none,none,none,none,some 5]
    a (Ty.poisoned (.vec 8 32))
  let c := Operation.insertelement b (.value 0#32) (.value 5#64)
  let d := Vector.zipWith Operation.and x maskD
  Vector.zipWith (Operation.add {nsw := true, nuw := true}) c d

def stepInstructions (x y : ⟦Ty.vec 8 32⟧) : ⟦Ty.vec 8 32⟧ :=
  let a := Vector.zipWith (Operation.lshr false) x (Ty.wrap (t := .vec 8 32) shifts)
  let b := Vector.zipWith (Operation.lshr false) y (Ty.wrap (t := .vec 8 32) shifts)
  let c := Operation.shufflevector #v[none,none,none,none,none,some 7,none,some 13] a b
  let d := Vector.zipWith Operation.and y maskD
  Vector.zipWith (Operation.add {nsw := true, nuw := true}) c d

def foldInstructions (x : ⟦Ty.vec 8 32⟧) : ⟦Ty.vec 8 32⟧ :=
  let a := Vector.zipWith (Operation.lshr false) x (Ty.wrap (t := .vec 8 32) shifts)
  let b := Vector.zipWith Operation.and a
    #v[.poison,.poison,.poison,.poison,.poison,.value 0#32,.poison,.value 15#32]
  let c := Operation.shufflevector #v[none,none,none,none,none,none,some 7,some 5]
    b (Ty.poisoned (.vec 8 32))
  let d : ⟦Ty.vec 4 64⟧ := Operation.bitcast (by decide) c
  let e : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) d
    #v[.poison,.poison,.poison,.value 19#64]
  let f : ⟦Ty.vec 8 32⟧ := Operation.bitcast (by decide) e
  Operation.shufflevector #v[none,none,none,none,none,some 6,none,some 7]
    f (Ty.poisoned (.vec 8 32))

theorem first_value (x : V32) :
    firstInstructions (Ty.wrap x) =
      pair (x[5] &&& 67108863#32) ((x[5] >>> 26)+(x[7] &&& 33554431#32)) := by
  have hz : Operation.add {nsw := true, nuw := true} (.value 0#32)
      (.value (x[5] &&& 67108863#32)) = .value (x[5] &&& 67108863#32) := by
    simpa using Normalization.add_small 0 (x[5] &&& 67108863#32)
      (by decide) (mask32_small _ _ (by decide))
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [firstInstructions, pair, maskD, shifts, Ty.wrap_vec,
    Operation.shufflevector, Operation.insertelement, Operation.lshr, Operation.and,
    hz, Normalization.carry_add25]
  all_goals rfl

theorem step_value (x y : V32) :
    stepInstructions (Ty.wrap x) (Ty.wrap y) =
      pair ((x[7] >>> 25)+(y[5] &&& 67108863#32))
        ((y[5] >>> 26)+(y[7] &&& 33554431#32)) := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [stepInstructions, pair, maskD, shifts, Ty.wrap_vec,
    Operation.shufflevector, Operation.lshr, Operation.and,
    Normalization.carry_add25, Normalization.carry_add26]
  all_goals rfl

theorem fold_value (x : V32) :
    foldInstructions (Ty.wrap x) = pair (top x[7]*19) 0 := by
  unfold foldInstructions
  dsimp only
  have h : Operation.shufflevector #v[none,none,none,none,none,none,some 7,some 5]
      (Vector.zipWith Operation.and
        (Vector.zipWith (Operation.lshr false) (Ty.wrap (t := .vec 8 32) x) (Ty.wrap (t := .vec 8 32) shifts))
        #v[.poison,.poison,.poison,.poison,.poison,.value 0#32,.poison,.value 15#32])
      (Ty.poisoned (.vec 8 32)) = sparse32 (top x[7]) 0 := by
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [Operation.shufflevector, Operation.lshr, Operation.and,
      shifts, sparse32, top, Ty.wrap_vec]
  rw [h, sparse_join]
  have hm : Vector.zipWith (Operation.mul {nsw := true, nuw := true})
      (sparse64 (0#32 ++ top x[7])) #v[.poison,.poison,.poison,.value 19#64] =
      sparse64 ((top x[7]).setWidth 64*19) := by
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [sparse64, zero_append_eq_wide, mul19_wide_value]
    all_goals rfl
  erw [hm, sparse_split]
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [Operation.shufflevector, sparse32, pair, top_mul_low, top_mul_high]

end Agave.Ed25519.Tables.Avx2Constructor.CacheNegation

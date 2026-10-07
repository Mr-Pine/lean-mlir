import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorNormalizationArithmetic
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionInstructions
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseRepresentation

/-! Poison-safe word operations for the constructor's parallel carry pass. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Normalization
open LeanMLIR.RIR Avx2PointAdd Avx2SquareNegateD
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] Ty.width

def shifts : V32 := #v[26,26,25,25,26,26,25,25]
def masks : V32 := #v[67108863,67108863,33554431,33554431,
  67108863,67108863,33554431,33554431]
def shifted (x : V32) : V32 := Vector.zipWith (· >>> ·) x shifts
def masked (x : V32) : V32 := Vector.zipWith (· &&& ·) x masks

def stepInstructions (x y : ⟦Ty.vec 8 32⟧) : ⟦Ty.vec 8 32⟧ :=
  let a := Vector.zipWith (Operation.lshr false) x (Ty.wrap (t := .vec 8 32) shifts)
  let b := Vector.zipWith (Operation.lshr false) y (Ty.wrap (t := .vec 8 32) shifts)
  let c := Operation.shufflevector
    #v[some 2,some 3,some 8,some 9,some 6,some 7,some 12,some 13] a b
  let d := Vector.zipWith Operation.and y (Ty.wrap (t := .vec 8 32) masks)
  Vector.zipWith (Operation.add {nsw := true, nuw := true}) c d

def step (x y : V32) : V32 :=
  #v[(x[2] >>> 25)+(y[0] &&& 67108863), (x[3] >>> 25)+(y[1] &&& 67108863),
     (y[0] >>> 26)+(y[2] &&& 33554431), (y[1] >>> 26)+(y[3] &&& 33554431),
     (x[6] >>> 25)+(y[4] &&& 67108863), (x[7] >>> 25)+(y[5] &&& 67108863),
     (y[4] >>> 26)+(y[6] &&& 33554431), (y[5] >>> 26)+(y[7] &&& 33554431)]

theorem add_small (x y : BitVec 32) (hx : x.toNat < 2^28) (hy : y.toNat < 2^28) :
    Operation.add {nsw := true, nuw := true} (.value x) (.value y) = .value (x+y) := by
  have hu : x.uaddOverflow y = false := by
    simp only [BitVec.uaddOverflow, decide_eq_false_iff_not]
    norm_num at hx hy ⊢
    omega
  simp [Operation.add, add32_small_flags x y hx hy, hu]

theorem shift_small (x : BitVec 32) (n : Nat) (hn : n = 25 ∨ n = 26) :
    (x >>> n).toNat < 2^28 := by
  have hx := x.isLt
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rcases hn with rfl | rfl <;> norm_num at hx ⊢ <;> omega

theorem carry_add26 (x y : BitVec 32) :
    Operation.add {nsw := true, nuw := true} (.value (x >>> 25))
      (.value (y &&& 67108863#32)) = .value ((x >>> 25)+(y &&& 67108863)) :=
  add_small _ _ (shift_small x 25 (Or.inl rfl)) (mask32_small y _ (by decide))

theorem carry_add25 (x y : BitVec 32) :
    Operation.add {nsw := true, nuw := true} (.value (x >>> 26))
      (.value (y &&& 33554431#32)) = .value ((x >>> 26)+(y &&& 33554431)) :=
  add_small _ _ (shift_small x 26 (Or.inr rfl)) (mask32_small y _ (by decide))

theorem step_value (x y : V32) :
    stepInstructions (Ty.wrap (t := .vec 8 32) x) (Ty.wrap y) = Ty.wrap (step x y) := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [stepInstructions, step, shifts, masks, Ty.wrap_vec,
    Operation.shufflevector, Operation.lshr, Operation.and, carry_add26, carry_add25]

def top (x : BitVec 32) : BitVec 32 := (x >>> 25) &&& 127

theorem top_bound (x : BitVec 32) : (top x).toNat < 128 := by
  have h : ((x >>> 25).toNat &&& 127) ≤ 127 := Nat.and_le_right
  change ((x >>> 25).toNat &&& 127) < 128
  omega

def foldInstructions (x : ⟦Ty.vec 8 32⟧) : ⟦Ty.vec 8 32⟧ :=
  let a := Vector.zipWith (Operation.lshr false) x (Ty.wrap (t := .vec 8 32) shifts)
  let b := Vector.zipWith Operation.and a
    (Ty.wrap (t := .vec 8 32) (#v[0,0,127,127,0,0,127,127] : V32))
  let c := Operation.shufflevector
    #v[some 2,some 0,some 3,some 1,some 6,some 4,some 7,some 5] b (Ty.poisoned (.vec 8 32))
  let d : ⟦Ty.vec 4 64⟧ := Operation.bitcast (by decide) c
  let e : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) d
    (Vector.replicate 4 (.value 19#64))
  let f : ⟦Ty.vec 8 32⟧ := Operation.bitcast (by decide) e
  Operation.shufflevector
    #v[some 0,some 2,some 1,some 3,some 4,some 6,some 5,some 7] f (Ty.poisoned (.vec 8 32))

def fold (x : V32) : V32 :=
  #v[top x[2]*19,top x[3]*19,0,0,top x[6]*19,top x[7]*19,0,0]

theorem top_mul_low (x : BitVec 32) :
    ((top x).setWidth 64 * 19#64).extractLsb' 0 32 = top x * 19 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb', BitVec.toNat_mul, wide_toNat]

theorem top_mul_high (x : BitVec 32) :
    ((top x).setWidth 64 * 19#64).extractLsb' 32 32 = 0 := by
  have h := top_bound x
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb', BitVec.toNat_mul, wide_toNat,
    BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.shiftRight_eq_div_pow]
  have hp : (top x).toNat * 19 < 2^32 := by omega
  norm_num only [Nat.reducePow, Nat.reduceMod, Nat.shiftRight_zero]
  norm_num at hp
  rw [Nat.mod_eq_of_lt (lt_trans hp (by norm_num)), Nat.div_eq_of_lt hp]
  rfl

theorem fold_value (x : V32) : foldInstructions (Ty.wrap (t := .vec 8 32) x) = Ty.wrap (fold x) := by
  unfold foldInstructions
  dsimp only
  have h : Operation.shufflevector
      #v[some 2,some 0,some 3,some 1,some 6,some 4,some 7,some 5]
      (Vector.zipWith Operation.and
        (Vector.zipWith (Operation.lshr false) (Ty.wrap (t := .vec 8 32) x) (Ty.wrap (t := .vec 8 32) shifts))
        (Ty.wrap (t := .vec 8 32) (#v[0,0,127,127,0,0,127,127] : V32))) (Ty.poisoned (.vec 8 32)) =
      Ty.wrap (#v[top x[2],0,top x[3],0,top x[6],0,top x[7],0] : V32) := by
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [Operation.shufflevector, Operation.lshr, Operation.and,
      Ty.wrap_vec, shifts, top]
  rw [h]
  erw [bitcast_join64]
  have hm : Vector.zipWith (Operation.mul {nsw := true, nuw := true})
      (Ty.wrap (t := .vec 4 64) (join64 (#v[top x[2],0,top x[3],0,top x[6],0,top x[7],0] : V32)))
      (Vector.replicate 4 (.value 19#64)) =
      Ty.wrap (t := .vec 4 64) (#v[(top x[2]).setWidth 64*19, (top x[3]).setWidth 64*19,
        (top x[6]).setWidth 64*19, (top x[7]).setWidth 64*19] : V64) := by
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [join64, Ty.wrap_vec, zero_append_eq_wide, mul19_wide_value]
  rw [hm]
  erw [bitcast_split32]
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [Operation.shufflevector, split32, fold, Ty.wrap_vec,
    top_mul_low, top_mul_high]

theorem top_mul_bound (x : BitVec 32) : (top x * 19).toNat < 2^28 := by
  have h := top_bound x
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  have hp : (top x).toNat * 19 < 2^28 := by omega
  change (top x).toNat * 19 % 4294967296 < 268435456
  norm_num at hp
  rw [Nat.mod_eq_of_lt (lt_trans hp (by norm_num))]
  exact hp

def firstInstructions (x y : ⟦Ty.vec 8 32⟧) : ⟦Ty.vec 8 32⟧ :=
  Vector.zipWith (Operation.add {nsw := true, nuw := true})
    (Vector.zipWith Operation.and y (Ty.wrap (t := .vec 8 32) masks))
    (foldInstructions x)

def first (x y : V32) : V32 := Vector.zipWith (· + ·) (masked y) (fold x)

theorem first_value (x y : V32) :
    firstInstructions (Ty.wrap x) (Ty.wrap y) = Ty.wrap (first x y) := by
  unfold firstInstructions
  rw [fold_value]
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [first, masked, masks, fold, Ty.wrap_vec, Operation.and]
  all_goals first
    | apply add_small
    | refine (add_small _ 0 (mask32_small _ _ (by decide)) (by decide)).trans ?_
      simp
  all_goals first
    | exact mask32_small _ _ (by decide)
    | exact top_mul_bound _
    | decide

end Agave.Ed25519.Tables.Avx2Constructor.Normalization

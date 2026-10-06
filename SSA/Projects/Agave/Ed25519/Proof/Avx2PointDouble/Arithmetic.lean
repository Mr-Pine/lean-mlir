import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.Reduction
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.Reduced
import SSA.Projects.Agave.Ed25519.Spec.PointArithmetic

/-! Caller-derived bounds for the AVX2 doubling schedule. These are integer
coefficient specifications; the connection to the extracted instructions is
stated separately. In particular the final multiplication is asymmetric:
its inputs do not satisfy the narrower `Field.MulBound` contract. -/
namespace Agave.Ed25519.Avx2PointDouble

abbrev Limbs := Fin 10 → Nat
abbrev Coordinates := Fin 4 → Limbs

def radix (i : Fin 10) : Nat := 2 ^ (if i.val % 2 = 0 then 26 else 25)
def slack : Nat := 2 ^ 18

def Reduced (a : Limbs) : Prop := ∀ i, a i < radix i + slack
def PointBound (p : Coordinates) : Prop := ∀ e, Reduced (p e)

/-- The exact radix-26/25 coefficients of twice the prime from constants.rs. -/
def twoP (i : Fin 10) : Nat :=
  2 * (radix i - if i.val = 0 then 19 else 1)

def prepare (p : Coordinates) : Coordinates :=
  ![p 0, p 1, p 2, fun i => p 0 i + p 1 i]

def squareStage (p : Coordinates) : Coordinates :=
  fun e => Avx2SquareNegateD.output (prepare p e) (e.val == 3)

/-- Physical lanes S5, S6, S8, S9. All subtraction is the source's lazy
coefficient subtraction from 2p, not subtraction modulo a machine word. -/
def mix (q : Coordinates) : Coordinates := ![
  fun i => q 0 i + q 1 i,
  fun i => q 0 i + (twoP i - q 1 i),
  fun i => q 0 i + 2 * q 2 i + (twoP i - q 1 i),
  fun i => q 0 i + q 1 i + q 3 i]

def left (q : Coordinates) : Coordinates := ![mix q 2, mix q 0, mix q 2, mix q 0]
def right (q : Coordinates) : Coordinates := ![mix q 3, mix q 1, mix q 1, mix q 3]

def leftLimit (i : Fin 10) : Nat := 5 * radix i + 3 * slack
def rightLimit (i : Fin 10) : Nat := 3 * radix i + 3 * slack

theorem prepare_bounded {p : Coordinates} (hp : PointBound p) (e : Fin 4) :
    Avx2SquareNegateD.Bounded (prepare p e) := by
  intro i
  have h0 := hp 0 i
  have h1 := hp 1 i
  have h2 := hp 2 i
  fin_cases e <;> simp only [prepare, Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals unfold Avx2SquareNegateD.inputLimit
  all_goals simp only [radix, slack] at h0 h1 h2
  all_goals split_ifs at * <;> omega

theorem squareStage_bounded {p : Coordinates} (hp : PointBound p) :
    PointBound (squareStage p) := by
  intro e i
  exact Avx2SquareNegateD.output_bounds (prepare_bounded hp e) _ i

theorem reduced_le_twoP {a : Limbs} (ha : Reduced a) (i : Fin 10) :
    a i ≤ twoP i := by
  have h := ha i
  unfold twoP radix slack at *
  split_ifs at * <;> norm_num at * <;> omega

theorem twoP_le_twice_radix (i : Fin 10) : twoP i ≤ 2 * radix i := by
  unfold twoP
  omega

/-- The source's coefficient subtraction cannot underflow. -/
theorem negate_lazy_exact {q : Coordinates} (hq : PointBound q) (i : Fin 10) :
    twoP i - q 1 i + q 1 i = twoP i :=
  Nat.sub_add_cancel (reduced_le_twoP (hq 1) i)

theorem left_bound {q : Coordinates} (hq : PointBound q) (e : Fin 4) (i : Fin 10) :
    left q e i < leftLimit i := by
  have h0 := hq 0 i
  have h1 := hq 1 i
  have h2 := hq 2 i
  have ht := twoP_le_twice_radix i
  have hs : twoP i - q 1 i ≤ twoP i := Nat.sub_le _ _
  fin_cases e <;> simp only [left, mix, Matrix.cons_val, Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals unfold leftLimit
  all_goals omega

theorem right_bound {q : Coordinates} (hq : PointBound q) (e : Fin 4) (i : Fin 10) :
    right q e i < rightLimit i := by
  have h0 := hq 0 i
  have h1 := hq 1 i
  have h3 := hq 3 i
  have ht := twoP_le_twice_radix i
  have hs : twoP i - q 1 i ≤ twoP i := Nat.sub_le _ _
  fin_cases e <;> simp only [right, mix, Matrix.cons_val, Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals unfold rightLimit
  all_goals omega

/-- The source doubling operands fit the actual multiplication helper's
asymmetric contract, including its u32 pre-scaling operations. -/
theorem multiply_left_bounded {q : Coordinates} (hq : PointBound q) (lane : Fin 4) :
    Avx2FieldMul.LeftBound (left q lane) := by
  intro i
  have h := left_bound hq lane i
  unfold leftLimit radix slack at h
  unfold Avx2FieldMul.leftLimit
  split_ifs at h ⊢ <;> norm_num at h ⊢ <;> omega

theorem multiply_right_bounded {q : Coordinates} (hq : PointBound q) (lane : Fin 4) :
    Avx2FieldMul.RightBound (right q lane) := by
  intro i
  have h := right_bound hq lane i
  unfold rightLimit radix slack at h
  unfold Avx2FieldMul.rightLimit
  split_ifs at h ⊢ <;> norm_num at h ⊢ <;> omega

/-- Both sums and all intermediate partial sums fit their actual u32 lanes. -/
theorem mix_fits_i32 {q : Coordinates} (hq : PointBound q) (e : Fin 4) (i : Fin 10) :
    mix q e i < 2 ^ 31 := by
  have h0 := left_bound hq 1 i
  have h1 := right_bound hq 1 i
  have h2 := left_bound hq 0 i
  have h3 := right_bound hq 0 i
  simp only [left, right, Matrix.cons_val] at h0 h1 h2 h3
  unfold leftLimit rightLimit radix slack at *
  fin_cases e <;> split_ifs at * <;> norm_num at * <;> omega

theorem mix_fits_u32 {q : Coordinates} (hq : PointBound q) (e : Fin 4) (i : Fin 10) :
    mix q e i < 2 ^ 32 :=
  lt_trans (mix_fits_i32 hq e i) (by norm_num)

/-- The exact worst-case convolution includes radix parity, rather than
multiplying an overly coarse uniform limb bound. -/
theorem limit_column_lt_u63 (k : Fin 10) :
    Avx2FieldMul.column leftLimit rightLimit k < 2 ^ 63 := by
  fin_cases k <;>
    norm_num [Avx2FieldMul.column, Avx2FieldMul.term, Avx2FieldMul.coefficient,
      Avx2FieldMul.rhsIndex, leftLimit, rightLimit, radix, slack, Fin.sum_univ_succ]

theorem column_mono {x y u v : Limbs} (hx : ∀ i, x i ≤ u i)
    (hy : ∀ i, y i ≤ v i) (k : Fin 10) :
    Avx2FieldMul.column x y k ≤ Avx2FieldMul.column u v k := by
  apply Finset.sum_le_sum
  intro i _
  unfold Avx2FieldMul.term
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (hx i)) (hy _)

theorem multiply_columns_bounded {q : Coordinates} (hq : PointBound q) (e : Fin 4) :
    Reduce64.ColumnsBound (Avx2FieldMul.column (left q e) (right q e)) := by
  intro k
  exact lt_of_le_of_lt
    (column_mono (fun i => Nat.le_of_lt (left_bound hq e i))
      (fun i => Nat.le_of_lt (right_bound hq e i)) k)
    (limit_column_lt_u63 k)

/-- Multiplication's RHS scaling is a genuine u32 multiplication. -/
theorem rhs_times19_fits_u32 {q : Coordinates} (hq : PointBound q)
    (e : Fin 4) (i : Fin 10) : 19 * right q e i < 2 ^ 32 := by
  have h := right_bound hq e i
  unfold rightLimit radix slack at h
  split_ifs at h <;> norm_num at h ⊢ <;> omega

/-- Multiplication doubles only odd LHS coefficients before widening. -/
theorem lhs_twice_fits_u32 {q : Coordinates} (hq : PointBound q)
    (e : Fin 4) (i : Fin 10) : 2 * left q e i < 2 ^ 32 := by
  have h := left_bound hq e i
  unfold leftLimit radix slack at h
  split_ifs at h <;> norm_num at h ⊢ <;> omega

/-- Exact integer coefficient schedule of AVX2 doubling. -/
def output (p : Coordinates) : Coordinates := fun e =>
  Avx2FieldMul.product (left (squareStage p) e) (right (squareStage p) e)

/-- Every doubling returns the same coefficient invariant it consumed. All
intermediate square/multiply/reduction bounds follow from that one invariant. -/
theorem output_bounded {p : Coordinates} (hp : PointBound p) : PointBound (output p) := by
  intro e i
  exact Reduce64.output_bounds _
    (multiply_columns_bounded (squareStage_bounded hp) e) i

end Agave.Ed25519.Avx2PointDouble

import SSA.Projects.Agave.Ed25519.Spec.PointArithmetic
import SSA.Projects.Agave.Ed25519.Spec.NAF

/-!
# The shared double-base scan and ladder

This is the control/algebra layer of `vartime_double_base::mul`, in
solana-ed25519 0.2.4. Both source backends scan from 255 down to 0, then execute
an inclusive descending ladder. Even an all-zero input executes digit 0.

The operation schedule below contains the actual sign branches and lookup
indices (`NafLookupTable::select(x)` indexes its array at `x / 2`). Its algebraic
refinement uses the proved point identities, not assumed field correctness.
The missing compiler-CFG, field-limb, NAF-array and table-construction bridges
are deliberately not hidden in this theorem.
-/
namespace Agave.Ed25519.DoubleBase

open PointArithmetic

abbrev Digits := Nat → Int
abbrev TableIndex := Bool × Nat

/-- Natural-index view of the proved source-position NAF specification. -/
def nafDigits (w n : Nat) : Digits := NAF.digits w 256 0 ⟨n, 0⟩

theorem nafDigits_source (w n : Nat) (i : Fin 256) :
    nafDigits w n i = NAF.sourceDigits w n i := rfl

/-- `false` denotes table A and `true` table B. -/
def digitOps (side : Bool) (digit : Int) : List (Operation TableIndex) :=
  if 0 < digit then [.add (side, digit.natAbs / 2)]
  else if digit < 0 then [.sub (side, digit.natAbs / 2)]
  else []

def roundOps (a b : Digits) (i : Nat) : List (Operation TableIndex) :=
  [.double] ++ digitOps false (a i) ++ digitOps true (b i)

/-- Inclusive ladder: execute n, n-1, ..., 0. -/
def ladder (a b : Digits) : Nat → List (Operation TableIndex)
  | 0 => roundOps a b 0
  | n + 1 => roundOps a b (n + 1) ++ ladder a b n

/-- Mirrors the source's initial descending scan, including its zero fallback. -/
def startIndex (a b : Digits) : Nat → Nat
  | 0 => 0
  | n + 1 => if a (n + 1) ≠ 0 ∨ b (n + 1) ≠ 0 then n + 1
      else startIndex a b n

/-- Counter form of the emitted scan: enter at 256, decrement before loading A,
then load B only when A is zero; the zero-index test prevents underflow. This
is an integer control model, not a claim about the RIR memory semantics. -/
def counterScan (a b : Digits) : Nat → Nat
  | 0 => 0
  | n + 1 => if a n ≠ 0 then n
      else if b n ≠ 0 ∨ n = 0 then n
      else counterScan a b n

theorem counterScan_eq_startIndex (a b : Digits) (n : Nat) :
    counterScan a b (n + 1) = startIndex a b n := by
  induction n with
  | zero => simp [counterScan, startIndex]
  | succ n ih =>
    rw [counterScan, startIndex, ih]
    by_cases ha : a (n + 1) = 0 <;> by_cases hb : b (n + 1) = 0 <;> simp [ha, hb]

def schedule (a b : Digits) : List (Operation TableIndex) :=
  ladder a b (startIndex a b 255)

theorem startIndex_le (a b : Digits) (n : Nat) : startIndex a b n ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [startIndex]; split_ifs <;> omega

theorem skipped_digits_zero (a b : Digits) (n i : Nat)
    (hlo : startIndex a b n < i) (hhi : i ≤ n) : a i = 0 ∧ b i = 0 := by
  induction n with
  | zero => simp [startIndex] at hlo; omega
  | succ n ih =>
    simp only [startIndex] at hlo
    split_ifs at hlo with h
    · omega
    · by_cases hi : i = n + 1
      · subst i; simpa only [not_or, ne_eq, not_not] using h
      · exact ih hlo (by omega)

theorem startIndex_nonzero (a b : Digits) (n : Nat)
    (h : startIndex a b n ≠ 0) :
    a (startIndex a b n) ≠ 0 ∨ b (startIndex a b n) ≠ 0 := by
  induction n with
  | zero => simp [startIndex] at h
  | succ n ih =>
    simp only [startIndex] at *
    split_ifs at * with hn
    · exact hn
    · exact ih h

@[simp] theorem startIndex_zero (n : Nat) : startIndex (fun _ => 0) (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [startIndex] using ih

@[simp] theorem digitOps_zero (side : Bool) : digitOps side 0 = [] := by
  simp [digitOps]

/-- All-zero scalars do one doubling at index zero, rather than an empty loop. -/
theorem schedule_zero : schedule (fun _ => 0) (fun _ => 0) = [.double] := by
  simp [schedule, ladder, roundOps]

theorem startIndex_top (a b : Digits) (n : Nat)
    (h : a (n + 1) ≠ 0 ∨ b (n + 1) ≠ 0) : startIndex a b (n + 1) = n + 1 := by
  simp [startIndex, h]

/-- Values outside the scanned prefix cannot affect the chosen start. -/
theorem startIndex_congr (a b a' b' : Digits) (n : Nat)
    (ha : ∀ i, i ≤ n → a i = a' i) (hb : ∀ i, i ≤ n → b i = b' i) :
    startIndex a b n = startIndex a' b' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [startIndex, ha (n + 1) (by omega), hb (n + 1) (by omega)]
    split_ifs
    · rfl
    · exact ih (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega))

theorem ladder_congr (a b a' b' : Digits) (n : Nat)
    (ha : ∀ i, i ≤ n → a i = a' i) (hb : ∀ i, i ≤ n → b i = b' i) :
    ladder a b n = ladder a' b' n := by
  induction n with
  | zero => simp [ladder, roundOps, ha 0 (by omega), hb 0 (by omega)]
  | succ n ih =>
    simp only [ladder, roundOps, ha (n + 1) (by omega), hb (n + 1) (by omega)]
    rw [ih (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega))]

/-- Equality of exactly the 256 array entries suffices for identical schedules. -/
theorem schedule_congr (a b a' b' : Digits)
    (ha : ∀ i, i < 256 → a i = a' i) (hb : ∀ i, i < 256 → b i = b' i) :
    schedule a b = schedule a' b' := by
  unfold schedule
  rw [startIndex_congr a b a' b' 255
    (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega))]
  apply ladder_congr
  · intro i hi; exact ha i (by have := startIndex_le a' b' 255; omega)
  · intro i hi; exact hb i (by have := startIndex_le a' b' 255; omega)

/-- Source table safety, including the maximum magnitude 15/127 and negative
digits. Oddness and the bound exclude zero and -128 at every selected index. -/
theorem lookup_index_safe (w : Nat) (hw : NAF.Supported w) (d : Int)
    (hlo : -(2 ^ (w - 1) : Int) < d) (hhi : d < (2 ^ (w - 1) : Int)) :
    d.natAbs / 2 < 2 ^ (w - 2) := by
  have habs : (d.natAbs : Int) = d ∨ (d.natAbs : Int) = -d := by
    rcases le_total 0 d with h | h
    · exact Or.inl (Int.natAbs_of_nonneg h)
    · exact Or.inr (Int.ofNat_natAbs_of_nonpos h)
  rcases hw with rfl | rfl <;> norm_num at * <;> omega

theorem naf_lookup_index_safe (w : Nat) (hw : NAF.Supported w)
    (s : NAF.State) (hc : s.carry ≤ 1) :
    (NAF.step w s).digit.natAbs / 2 < 2 ^ (w - 2) := by
  obtain ⟨hlo, hhi, _⟩ := NAF.digit_bounds w hw s hc
  exact lookup_index_safe w hw _ hlo hhi

theorem nafDigits_lookup_index_safe (w : Nat) (hw : NAF.Supported w) (n i : Nat) :
    (nafDigits w n i).natAbs / 2 < 2 ^ (w - 2) := by
  obtain ⟨hlo, hhi, _⟩ := NAF.digits_bounds w hw 256 0 ⟨n, 0⟩ (by norm_num) i
  exact lookup_index_safe w hw _ hlo hhi

/-- Recursive formulation of the source's loop state, preserving the order:
double, signed A addition, signed B addition, then the next lower digit. -/
def run {State : Type*} (step : State → Operation TableIndex → State)
    (a b : Digits) : Nat → State → State
  | 0, q => (roundOps a b 0).foldl step q
  | n + 1, q => run step a b n ((roundOps a b (n + 1)).foldl step q)

theorem run_eq_fold {State : Type*} (step : State → Operation TableIndex → State)
    (a b : Digits) (n : Nat) (q : State) :
    run step a b n q = (ladder a b n).foldl step q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih => simp only [run, ladder, List.foldl_append, ih]

section Field
variable {K : Type*} [Field K]

/-- Both source loops start at (0,1,1); the scalar ghost T coordinate is zero. -/
def identityPoint : Extended K := ⟨0, 1, 1, 0⟩

/-- Total view of the two finite source tables. The fallback is never selected
by a source NAF digit, by `nafDigits_lookup_index_safe`; giving both
representations the same fallback avoids any off-range table premise. -/
def finiteTable (table : Fin 8 ⊕ Fin 64 → Extended K) : TableIndex → Extended K
  | (side, i) => if side then
      if h : i < 64 then table (.inr ⟨i, h⟩) else identityPoint
    else
      if h : i < 8 then table (.inl ⟨i, h⟩) else identityPoint

theorem finiteTable_related (serialTable avx2Table : Fin 8 ⊕ Fin 64 → Extended K)
    (hTable : ∀ i, Related (serialTable i) (avx2Table i)) (i : TableIndex) :
    Related (finiteTable serialTable i) (finiteTable avx2Table i) := by
  rcases i with ⟨side, i⟩
  cases side with
  | false =>
    by_cases hi : i < 8
    · simpa [finiteTable, hi] using hTable (.inl ⟨i, hi⟩)
    · simpa [finiteTable, hi] using (related_refl (identityPoint : Extended K))
  | true =>
    by_cases hi : i < 64
    · simpa [finiteTable, hi] using hTable (.inr ⟨i, hi⟩)
    · simpa [finiteTable, hi] using (related_refl (identityPoint : Extended K))

/-- The source's initial scan and entire inclusive loop preserve the proved
projective relation. Exact primitive premises: related initial points and
related entries in the two lookup tables; the formulas themselves are proved
by `PointArithmetic.double_related` and `add_related`.

This theorem does not assert that arbitrary limb machine values implement
these formulas; the RIR refinement must establish that independently. -/
theorem double_base_related (d : K)
    (hd : (121666 : K) * d = -121665) (hc : (121666 : K) ≠ 0)
    (serialTable avx2Table : TableIndex → Extended K)
    (hTable : ∀ i, Related (serialTable i) (avx2Table i))
    (a b : Digits) {P Q : Extended K} (hPQ : Related P Q) :
    Related
      (run (serialStep d serialTable) a b (startIndex a b 255) P)
      (run (avx2Step avx2Table) a b (startIndex a b 255) Q) := by
  simp only [run_eq_fold]
  exact schedule_related d hd hc serialTable avx2Table hTable _ hPQ

theorem double_base_affine_eq (d : K)
    (hd : (121666 : K) * d = -121665) (hc : (121666 : K) ≠ 0)
    (serialTable avx2Table : TableIndex → Extended K)
    (hTable : ∀ i, Related (serialTable i) (avx2Table i))
    (a b : Digits) {P Q : Extended K} (hPQ : Related P Q) :
    affine (run (avx2Step avx2Table) a b (startIndex a b 255) Q) =
      affine (run (serialStep d serialTable) a b (startIndex a b 255) P) :=
  related_affine_eq (double_base_related d hd hc serialTable avx2Table hTable a b hPQ)

/-- Includes the scalar implementation's final `ProjectivePoint::as_extended`.
The observation is any common encoder of affine coordinates, so this covers
canonical compression once its machine-code refinement is supplied. -/
theorem double_base_compress_eq {Bytes : Type*} (encode : K × K → Bytes) (d : K)
    (hd : (121666 : K) * d = -121665) (hc : (121666 : K) ≠ 0)
    (serialTable avx2Table : TableIndex → Extended K)
    (hTable : ∀ i, Related (serialTable i) (avx2Table i))
    (a b : Digits) {P Q : Extended K} (hPQ : Related P Q) :
    compressWith encode (run (avx2Step avx2Table) a b (startIndex a b 255) Q) =
      compressWith encode (projectiveAsExtended
        (run (serialStep d serialTable) a b (startIndex a b 255) P)) := by
  simp only [compressWith, affine_projectiveAsExtended]
  rw [double_base_affine_eq d hd hc serialTable avx2Table hTable a b hPQ]

/-- Instantiation at the actual initial coordinates, fixed curve parameter and
source NAF widths. Only the representation relation for table entries and the
field's nonzero denominator remain as algebraic premises. -/
theorem double_base_naf_compress_eq {Bytes : Type*} (encode : K × K → Bytes)
    (hc : (121666 : K) ≠ 0)
    (serialTable avx2Table : TableIndex → Extended K)
    (hTable : ∀ i, Related (serialTable i) (avx2Table i)) (a b : Nat) :
    compressWith encode
      (run (avx2Step avx2Table) (nafDigits 5 a) (nafDigits 8 b)
        (startIndex (nafDigits 5 a) (nafDigits 8 b) 255) identityPoint) =
    compressWith encode (projectiveAsExtended
      (run (serialStep (-121665 / 121666) serialTable) (nafDigits 5 a) (nafDigits 8 b)
        (startIndex (nafDigits 5 a) (nafDigits 8 b) 255) identityPoint)) :=
  double_base_compress_eq encode _ (parameter_relation hc) hc serialTable avx2Table
    hTable _ _ (related_refl identityPoint)

end Field
end Agave.Ed25519.DoubleBase

import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ByteControl
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.Control
import SSA.Projects.Agave.Ed25519.Spec.NAF

/-!
# The emitted digit-control instruction network

This file executes the actual RIR scalar operations between a loaded digit and
the selected point-operation call. The signed comparison, wrapping negation,
sign extension, logical shift and both table guards are retained. A failed
guard or an unrecognized switch case produces poison. The source NAF bounds
prove that neither happens, without a premise about a loaded digit's index.

This is an instruction-network lemma, not yet a `SerialCFG.program` or
`Avx2CFG.program` whole-function execution theorem. Connecting the loaded
bytes and the selected memory records belongs to the memory/CFG refinement.
-/
namespace Agave.Ed25519.DoubleBase.Execution

open LeanMLIR.RIR

abbrev PointOp := PointArithmetic.Operation TableIndex

deriving instance DecidableEq for PointArithmetic.Operation

/-- The byte written by the NAF emitter for one output position. -/
def nafByte (w n i : Nat) : BitVec 8 := BitVec.ofInt 8 (nafDigits w n i)

theorem nafByte_toInt (w : Nat) (hw : NAF.Supported w) (n i : Nat) :
    (nafByte w n i).toInt = nafDigits w n i := by
  have h := NAF.digits_bounds w hw 256 0 ⟨n, 0⟩ (by norm_num) i
  change -(2 ^ (w - 1) : Int) < nafDigits w n i ∧
    nafDigits w n i < (2 ^ (w - 1) : Int) ∧ _ at h
  apply BitVec.toInt_ofInt_eq_self (by decide)
  · rcases hw with rfl | rfl <;> norm_num at h ⊢ <;> omega
  · rcases hw with rfl | rfl <;> norm_num at h ⊢ <;> omega

theorem nafByte_ne_neg128 (w : Nat) (hw : NAF.Supported w) (n i : Nat) :
    nafByte w n i ≠ 128#8 := by
  intro h
  have hvalue := nafByte_toInt w hw n i
  have hb := NAF.digits_bounds w hw 256 0 ⟨n, 0⟩ (by norm_num) i
  change -(2 ^ (w - 1) : Int) < nafDigits w n i ∧
    nafDigits w n i < (2 ^ (w - 1) : Int) ∧ _ at hb
  rw [h] at hvalue
  rcases hw with rfl | rfl <;> norm_num at hb hvalue <;> omega

theorem nafByte_lookup (w : Nat) (hw : NAF.Supported w) (n i : Nat) :
    compiledLookup (nafByte w n i) = (nafDigits w n i).natAbs / 2 := by
  rw [compiledLookup_correct _ (nafByte_ne_neg128 w hw n i), nafByte_toInt w hw]

/-- The literal `icmp ult magnitude,16` and `icmp sgt magnitude,-1` guards
in the width-five and width-eight branches respectively. -/
def indexGuard (basepoint : Bool) (magnitude : BitVec 8) : PoisonOr (BitVec 1) :=
  if basepoint then Operation.icmp .sgt (.value magnitude) (.value (-1))
  else Operation.icmp .ult (.value magnitude) (.value 16)

/-- The instruction sequence common to the negative and positive cases.
The negative case has already executed its wrapping i8 subtraction. -/
def selectIndex (basepoint subtract : Bool) (magnitude : BitVec 8) :
    PoisonOr (List PointOp) := do
  let wide : BitVec 64 ← Operation.sext (.value magnitude)
  let index ← Operation.lshr false (.value wide) (.value 1)
  let guard ← indexGuard basepoint magnitude
  if guard = 1#1 then
    return [if subtract then PointArithmetic.Operation.sub (basepoint, index.toNat)
      else PointArithmetic.Operation.add (basepoint, index.toNat)]
  else .poison

/-- The exact scmp/switch cases. The default reaches `llvm.unreachable`.
All comparisons are on bytes, and the negative case retains wrapping negation.
The branch-local point conversions are not represented by this control slice. -/
def digitBranch (basepoint : Bool) (digit : PoisonOr (BitVec 8)) :
    PoisonOr (List PointOp) := do
  let sign : BitVec 8 ← Operation.cmp true digit (.value 0)
  if sign = -1 then
    let magnitude ← Operation.sub {} (.value 0) digit
    selectIndex basepoint true magnitude
  else if sign = 0 then
    return []
  else if sign = 1 then
    let magnitude ← digit
    selectIndex basepoint false magnitude
  else .poison

/-- Checked for all 256 input bytes, including negative even values; oddness
is unnecessary for control safety and is used only for table interpretation. -/
theorem digitBranch_width5 : ∀ digit : BitVec 8,
    -16 < digit.toInt → digit.toInt < 16 →
    digitBranch false (.value digit) = .value (digitOps false digit.toInt) := by
  decide +kernel

theorem digitBranch_width8 : ∀ digit : BitVec 8,
    -128 < digit.toInt → digit.toInt < 128 →
    digitBranch true (.value digit) = .value (digitOps true digit.toInt) := by
  decide +kernel

/-- Both emitted sign-switch and panic successors are excluded by the proved
NAF construction; there is no digit-bounds or table-bounds assumption here. -/
theorem digitBranch_naf5 (n i : Nat) :
    digitBranch false (.value (nafByte 5 n i)) = .value (digitOps false (nafDigits 5 n i)) := by
  have hb := NAF.digits_bounds 5 (Or.inl rfl) 256 0 ⟨n, 0⟩ (by norm_num) i
  change -(2 ^ (5 - 1) : Int) < nafDigits 5 n i ∧
    nafDigits 5 n i < (2 ^ (5 - 1) : Int) ∧ _ at hb
  have hround := nafByte_toInt 5 (Or.inl rfl) n i
  norm_num at hb
  simpa only [hround] using digitBranch_width5 (nafByte 5 n i)
    (by rw [hround]; exact hb.1) (by rw [hround]; exact hb.2.1)

theorem digitBranch_naf8 (n i : Nat) :
    digitBranch true (.value (nafByte 8 n i)) = .value (digitOps true (nafDigits 8 n i)) := by
  have hb := NAF.digits_bounds 8 (Or.inr rfl) 256 0 ⟨n, 0⟩ (by norm_num) i
  change -(2 ^ (8 - 1) : Int) < nafDigits 8 n i ∧
    nafDigits 8 n i < (2 ^ (8 - 1) : Int) ∧ _ at hb
  have hround := nafByte_toInt 8 (Or.inr rfl) n i
  norm_num at hb
  simpa only [hround] using digitBranch_width8 (nafByte 8 n i)
    (by rw [hround]; exact hb.1) (by rw [hround]; exact hb.2.1)

/-- Exactly the two instruction-control slices around a doubling. -/
def roundBranches (a b : BitVec 8) : PoisonOr (List PointOp) := do
  let aOps ← digitBranch false (.value a)
  let bOps ← digitBranch true (.value b)
  return [PointArithmetic.Operation.double] ++ aOps ++ bOps

theorem roundBranches_naf (a b i : Nat) :
    roundBranches (nafByte 5 a i) (nafByte 8 b i) =
      .value (roundOps (nafDigits 5 a) (nafDigits 8 b) i) := by
  simp only [roundBranches, digitBranch_naf5, digitBranch_naf8, PoisonOr.value_bind,
    PoisonOr.pure_def, roundOps]

/-- The pre-load decrement in the initial scan is signed-no-wrap, including
the first 256→255 step and the final 1→0 step. -/
theorem scan_decrement : ∀ i : Fin 256,
    Operation.add { nsw := true } (.value (BitVec.ofNat 64 (i.val + 1)))
      (.value (-1)) = .value (BitVec.ofNat 64 i.val) := by
  decide +kernel

end Agave.Ed25519.DoubleBase.Execution

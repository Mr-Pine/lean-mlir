import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionArithmetic
import SSA.Projects.Agave.Ed25519.Proof.SHA512.ScheduleSpec

/-! Arithmetic of the pinned scalar C SHA implementation. These lemmas use the
actual expression ordering of its two core loops and append/finish branches.
They are independent of memory execution; no compression contract is assumed. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution
open Agave.Ed25519.SHA512
open Agave.Ed25519.SHA512.Spec

/-- C's disjoint OR implements SHA's choice function. -/
theorem source_choose (e f g : Word) :
    (e &&& f) ||| (g &&& (e ^^^ (-1 : Word))) = choose e f g := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [choose, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_xor, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  have hm : (-1 : Word).getLsbD i = true := by
    change (BitVec.allOnes 64).getLsbD i = true
    simp only [BitVec.getLsbD_allOnes, hi, decide_true]
  rw [hm]
  cases e.getLsbD i <;> cases f.getLsbD i <;> cases g.getLsbD i <;> rfl

theorem source_majority (a b c : Word) :
    (a &&& (b ^^^ c)) ^^^ (b &&& c) = majority a b c := by
  simpa only [BitVec.and_comm, BitVec.xor_comm] using
    Compression.Avx2ExecutionArithmetic.majority_source a b c

/-- Exact addition order in bb2 (the first sixteen rounds). -/
def firstRound (s : State) (word constant : Word) : State :=
  let choice := (s.e &&& s.f) ||| (s.g &&& (s.e ^^^ (-1 : Word)))
  let t1 := choice + s.h + bigSigma1 s.e + word + constant
  let t2 := bigSigma0 s.a + ((s.a &&& (s.b ^^^ s.c)) ^^^ (s.b &&& s.c))
  ⟨t2 + t1, s.a, s.b, s.c, t1 + s.d, s.e, s.f, s.g⟩

/-- Exact addition order in bb3 (the remaining sixty-four rounds). -/
def laterRound (s : State) (word constant : Word) : State :=
  let choice := (s.e &&& s.f) ||| (s.g &&& (s.e ^^^ (-1 : Word)))
  let t1 := choice + s.h + bigSigma1 s.e + constant + word
  let t2 := bigSigma0 s.a + ((s.a &&& (s.b ^^^ s.c)) ^^^ (s.b &&& s.c))
  ⟨t2 + t1, s.a, s.b, s.c, t1 + s.d, s.e, s.f, s.g⟩

theorem firstRound_eq (s : State) (word constant : Word) :
    firstRound s word constant = Spec.round s word constant := by
  simp only [firstRound, Spec.round, source_choose, source_majority]
  congr 1 <;> ac_rfl

theorem laterRound_eq (s : State) (word constant : Word) :
    laterRound s word constant = Spec.round s word constant := by
  simp only [laterRound, Spec.round, source_choose, source_majority]
  congr 1 <;> ac_rfl

/-- C stores W[t] over W[t-16], after reading the four circular slots. -/
def scheduleWord (w16 w15 w7 w2 : Word) : Word :=
  smallSigma0 w15 + w7 + w16 + smallSigma1 w2

theorem scheduleWord_eq (w16 w15 w7 w2 : Word) :
    scheduleWord w16 w15 w7 w2 =
      smallSigma1 w2 + w7 + smallSigma0 w15 + w16 := by
  unfold scheduleWord
  ac_rfl

theorem scheduleWord_spec (block : Challenge.Bytes) (t : Nat)
    (hlo : 16 ≤ t) (hhi : t < 80) :
    scheduleWord ((schedule block).getD (t - 16) 0)
      ((schedule block).getD (t - 15) 0) ((schedule block).getD (t - 7) 0)
      ((schedule block).getD (t - 2) 0) = (schedule block).getD t 0 := by
  rw [scheduleWord_eq]
  simpa only [show 16 + (t - 16) = t by omega,
    show t - 16 + 14 = t - 2 by omega,
    show t - 16 + 9 = t - 7 by omega,
    show t - 16 + 1 = t - 15 by omega] using
      (schedule_recurrence block (t - 16) (by omega)).symm

/-- The exact low/high counter update from append, including low carry. -/
def appendLow (lo size : Word) : Word := lo + (size <<< 3)
def appendHigh (hi lo size : Word) : Word :=
  hi + (size >>> 61) + (if (appendLow lo size).ult lo then 1 else 0)

theorem append_counter (hi lo size : Word) :
    appendHigh hi lo size ++ appendLow lo size =
      (hi ++ lo) + (size.setWidth 128 <<< 3) := by
  have concatNat (a b : Word) : (a ++ b).toNat = a.toNat * 2 ^ 64 + b.toNat := by
    rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]
  apply BitVec.eq_of_toNat_eq
  simp only [concatNat, BitVec.toNat_add]
  have hh := hi.isLt
  have hl := lo.isLt
  have hs := size.isLt
  simp only [appendHigh, appendLow, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, BitVec.ult] at *
  split_ifs <;> norm_num at * <;> omega

/-- Full-block quotient and trailing bytes partition the original byte count. -/
theorem append_remainder (size : Word) :
    (size &&& 127).toNat = size.toNat % 128 := by
  change size.toNat &&& (2 ^ 7 - 1) = size.toNat % 2 ^ 7
  exact Nat.and_two_pow_sub_one_eq_mod size.toNat 7

theorem append_partition (size : Word) :
    ((size >>> 7) <<< 7) + (size &&& 127) = size := by
  apply BitVec.eq_of_toNat_eq
  have hs := size.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, append_remainder]
  norm_num at *
  omega

theorem append_aligned_mask (size : Word) :
    size &&& (-128 : Word) = ((size >>> 7) <<< 7) := by
  simpa only [show (BitVec.allOnes 64 <<< 7) = (-128 : Word) by decide] using
    (BitVec.shiftLeft_ushiftRight (x := size) (n := 7)).symm

theorem append_remainder_bound (size : Word) :
    (size &&& 127).toNat < 128 := by
  rw [append_remainder]
  omega

theorem append_core_count (size : Word) (h : 128 ≤ size.toNat) :
    0 < (size >>> 7).toNat ∧ (size >>> 7).toNat < 2 ^ 57 := by
  have hs := size.isLt
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  constructor
  · omega
  · omega

/-- The scalar C's compare has the same 112-byte cutoff as the shared padder. -/
theorem finish_two_blocks (used : Word) (h : used.toNat < 128) :
    (112#64).ult (used + 1) = true ↔ 112 ≤ used.toNat := by
  simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_add,
    BitVec.toNat_ofNat]
  norm_num
  have hu : used.toNat + 1 < 2 ^ 64 := by omega
  norm_num at hu
  rw [Nat.mod_eq_of_lt hu]
  omega

/-- Both memset lengths are nonnegative and cover exactly the required zeros. -/
theorem finish_padding_counts (used : Nat) (h : used < 128) :
    (used + 1 ≤ 112 → 112 - (used + 1) = 111 - used) ∧
    (112 < used + 1 → (127 - used) + 112 = 239 - used) := by omega

end Agave.Ed25519.Bridge.FiredancerSHAExecution

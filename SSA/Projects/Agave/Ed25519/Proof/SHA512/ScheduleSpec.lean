import SSA.Projects.Agave.Ed25519.Proof.SHA512.CompressionSpec
import Mathlib.Data.List.GetD

/-! Index and recurrence facts for the independent append-only schedule.
These make the intended FIPS recurrence explicit without assuming a correct
rolling/vector implementation or relying on the out-of-range default. -/

namespace Agave.Ed25519.SHA512.Spec

open Agave.Ed25519.Bridge.Challenge

theorem schedulePrefix_getD_old (block : Bytes) (n k i : Nat) (hi : i < 16 + n) :
    (schedulePrefix block (n + k)).getD i 0 = (schedulePrefix block n).getD i 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, schedulePrefix,
      List.getD_append _ _ _ _ (by simp only [schedulePrefix_length]; omega)]
    exact ih

theorem schedule_getD_prefix (block : Bytes) (n i : Nat)
    (hn : n ≤ 64) (hi : i < 16 + n) :
    (schedule block).getD i 0 = (schedulePrefix block n).getD i 0 := by
  unfold schedule
  have hsum : n + (64 - n) = 64 := by omega
  simpa only [hsum] using schedulePrefix_getD_old block n (64 - n) i hi

/-- The first sixteen schedule words are the original big-endian words. -/
theorem schedule_initial (block : Bytes) (i : Nat) (hi : i < 16) :
    (schedule block).getD i 0 = readWordBE block i := by
  rw [schedule_getD_prefix block 0 i (by decide) (by omega)]
  simp only [schedulePrefix, messageWords]
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

/-- For 16 ≤ t < 80, the complete schedule satisfies the independent
four-word recurrence. All four source indices are proved in range. -/
theorem schedule_recurrence (block : Bytes) (n : Nat) (hn : n < 64) :
    (schedule block).getD (16 + n) 0 =
      smallSigma1 ((schedule block).getD (n + 14) 0) +
      (schedule block).getD (n + 9) 0 +
      smallSigma0 ((schedule block).getD (n + 1) 0) +
      (schedule block).getD n 0 := by
  rw [schedule_getD_prefix block (n + 1) (16 + n) (by omega) (by omega)]
  rw [schedulePrefix,
    List.getD_append_right _ _ _ _ (by simp only [schedulePrefix_length]; omega)]
  simp only [schedulePrefix_length, Nat.sub_self, List.getD_cons_zero]
  rw [schedule_getD_prefix block n (n + 14) (by omega) (by omega),
    schedule_getD_prefix block n (n + 9) (by omega) (by omega),
    schedule_getD_prefix block n (n + 1) (by omega) (by omega),
    schedule_getD_prefix block n n (by omega) (by omega)]

end Agave.Ed25519.SHA512.Spec

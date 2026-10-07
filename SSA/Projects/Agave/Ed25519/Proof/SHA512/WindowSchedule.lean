import SSA.Projects.Agave.Ed25519.Proof.SHA512.ScheduleSpec
import SSA.Projects.Agave.Ed25519.Proof.SHA512.ScheduleArithmetic

/-! The AVX schedule advances a sixteen-word window by two words. This
source-level arithmetic invariant is independent of register packing and
memory. An execution refinement must separately connect the imported SIMD
operations to `avxWindowStep`; this file does not assume that connection.
-/

namespace Agave.Ed25519.SHA512.Spec

open Agave.Ed25519.Bridge.Challenge

abbrev Window := Fin 16 → Word

def specWindow (block : Bytes) (start : Nat) : Window :=
  fun i => (schedule block).getD (start + i.val) 0

def initialWindow (block : Bytes) : Window := fun i => readWordBE block i.val

/-- Two lanes computed by `sha512_update_x_avx`. ALIGNR selects q[1],q[2]
and q[9],q[10]; each lane then uses the same scalar shift/xor network. -/
def avxWindowPair (q : Window) : Word × Word :=
  (q 0 + q 9 + avxSmallSigma0 (q 1) + avxSmallSigma1 (q 14),
   q 1 + q 10 + avxSmallSigma0 (q 2) + avxSmallSigma1 (q 15))

/-- Rotate the eight two-word registers, installing the newly computed pair
at the end. Indices are bounded explicitly, with no out-of-range defaults. -/
def avxWindowStep (q : Window) : Window := fun i =>
  if h : i.val < 14 then q ⟨i.val + 2, by omega⟩
  else if i.val = 14 then (avxWindowPair q).1 else (avxWindowPair q).2

theorem initialWindow_eq (block : Bytes) : initialWindow block = specWindow block 0 := by
  funext i
  simpa [initialWindow, specWindow] using (schedule_initial block i.val i.isLt).symm

theorem avxWindowPair_spec (block : Bytes) (start : Nat) (hstart : start + 1 < 64) :
    avxWindowPair (specWindow block start) =
      ((schedule block).getD (start + 16) 0,
       (schedule block).getD (start + 17) 0) := by
  apply Prod.ext
  · simpa [avxWindowPair, specWindow, avxScheduleWord_eq,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (schedule_recurrence block start (by omega)).symm
  · simpa [avxWindowPair, specWindow, avxScheduleWord_eq,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (schedule_recurrence block (start + 1) hstart).symm

/-- The generated pair and rotated old lanes form exactly the next FIPS
window. Only the round-index bound is needed; message bytes are arbitrary. -/
theorem avxWindowStep_spec (block : Bytes) (start : Nat) (hstart : start + 1 < 64) :
    avxWindowStep (specWindow block start) = specWindow block (start + 2) := by
  funext i
  by_cases hi : i.val < 14
  · simp [avxWindowStep, hi, specWindow, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  · have hi' : i.val = 14 ∨ i.val = 15 := by have := i.isLt; omega
    rcases hi' with hi' | hi'
    · simp [avxWindowStep, hi, hi', avxWindowPair_spec block start hstart,
        specWindow, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    · simp [avxWindowStep, hi, hi', avxWindowPair_spec block start hstart,
        specWindow, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

def avxWindows (block : Bytes) : Nat → Window
  | 0 => initialWindow block
  | n + 1 => avxWindowStep (avxWindows block n)

/-- All thirty-two pair updates used by the one-block AVX path satisfy the
same invariant, including the final W[64..79] window. -/
theorem avxWindows_eq (block : Bytes) (steps : Nat) (hsteps : steps ≤ 32) :
    avxWindows block steps = specWindow block (2 * steps) := by
  induction steps with
  | zero => simpa [avxWindows] using initialWindow_eq block
  | succ steps ih =>
    rw [avxWindows, ih (by omega)]
    simpa [Nat.mul_add, Nat.add_assoc] using
      avxWindowStep_spec block (2 * steps) (by omega)

end Agave.Ed25519.SHA512.Spec

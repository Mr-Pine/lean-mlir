/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.Staging

/-!
An assumption-free serial-fallback congruence theorem for the exact
`stage_part` / `spill_current` call sequence in Agave `batch.rs`.

This deliberately does not identify a streaming hasher with the concatenation
of its input bytes: update need not be associative, partition-independent, or
even preserve its state on an empty input.  Thus it proves equality for the
same part trace, without assuming a BLAKE3 streaming theorem.

The reset in `spill_current` is represented by the common `initial` value.
This records the ordinary unkeyed Hasher.reset contract, rather than treating
reset as an arbitrary potentially history-sensitive transformation.
-/
namespace AgaveSerialStreaming

open AgaveStaging

structure Hasher (State Result : Type) where
  initial : State
  update : State → Message → State
  finalize : State → Result

structure Active (State : Type) where
  staged : Message
  serial : State
  spilled : Bool

/-- Hasher contents may differ while no message has spilled. Scalar partial
    flushes and full SIMD flushes do leave different dirty contents in Rust. -/
def Agree {State : Type} (a b : Active State) : Prop :=
  a.staged = b.staged ∧ a.spilled = b.spilled ∧
  (a.spilled = true → a.serial = b.serial)

def fresh {State : Type} (dirty : State) : Active State := ⟨[], dirty, false⟩

/-- Exact call sequence, including update([]) on an immediately spilling
    whole message. No lane count occurs in this code or its guard. -/
def part {State Result : Type} (h : Hasher State Result)
    (s : Active State) (bytes : Message) : Active State :=
  if s.spilled then
    { s with serial := h.update s.serial bytes }
  else if s.staged.length + bytes.length ≤ 1024 then
    { s with staged := s.staged ++ bytes }
  else
    ⟨[], h.update (h.update h.initial s.staged) bytes, true⟩

def parts {State Result : Type} (h : Hasher State Result)
    (s : Active State) (input : List Message) : Active State :=
  input.foldl (part h) s

def result {State Result : Type} (h : Hasher State Result)
    (shortHash : Message → Result) (s : Active State) : Result :=
  if s.spilled then h.finalize s.serial else shortHash s.staged

theorem fresh_agree {State : Type} (dirty₁ dirty₂ : State) :
    Agree (fresh dirty₁) (fresh dirty₂) := by
  simp [Agree, fresh]

theorem part_agree {State Result : Type} (h : Hasher State Result)
    (a b : Active State) (bytes : Message) (hab : Agree a b) :
    Agree (part h a bytes) (part h b bytes) := by
  rcases a with ⟨ma, sa, pa⟩
  rcases b with ⟨mb, sb, pb⟩
  rcases hab with ⟨hm, hp, hs⟩
  simp only at hm hp hs
  subst mb
  subst pb
  cases pa
  · simp only [part, Bool.false_eq_true, ↓reduceIte]
    split <;> simp [Agree]
  · have heq : sa = sb := hs rfl
    subst sb
    simp [part, Agree]

theorem parts_agree {State Result : Type} (h : Hasher State Result)
    (input : List Message) (a b : Active State) (hab : Agree a b) :
    Agree (parts h a input) (parts h b input) := by
  induction input generalizing a b with
  | nil => exact hab
  | cons bytes input ih =>
    exact ih (part h a bytes) (part h b bytes) (part_agree h a b bytes hab)

theorem result_agree {State Result : Type} (h : Hasher State Result)
    (shortHash : Message → Result) (a b : Active State) (hab : Agree a b) :
    result h shortHash a = result h shortHash b := by
  rcases hab with ⟨hm, hp, hs⟩
  unfold result
  rw [← hp]
  cases ha : a.spilled
  · simp [hm]
  · simp [hs ha]

/-- Dirty serial state can differ arbitrarily across the reference/AVX2/AVX512
    implementations before a new message. The same exact public add_part trace
    still yields the same result, for any streaming implementation whatsoever.
    In particular there is no premise asserting partition independence. -/
theorem same_parts_same_result {State Result : Type} (h : Hasher State Result)
    (shortHash : Message → Result) (input : List Message) (dirty₁ dirty₂ : State) :
    result h shortHash (parts h (fresh dirty₁) input) =
      result h shortHash (parts h (fresh dirty₂) input) :=
  result_agree h shortHash _ _ (parts_agree h input _ _ (fresh_agree _ _))

/-- The theorem permits three completely unrelated leftover Hasher states. -/
theorem reference_eq_avx2_eq_avx512 {State Result : Type} (h : Hasher State Result)
    (shortHash : Message → Result) (input : List Message)
    (dirty₁ dirty₈ dirty₁₆ : State) :
    let r₁ := result h shortHash (parts h (fresh dirty₁) input)
    let r₈ := result h shortHash (parts h (fresh dirty₈) input)
    let r₁₆ := result h shortHash (parts h (fresh dirty₁₆) input)
    r₁ = r₈ ∧ r₈ = r₁₆ := by
  exact ⟨same_parts_same_result h shortHash input dirty₁ dirty₈,
    same_parts_same_result h shortHash input dirty₈ dirty₁₆⟩

end AgaveSerialStreaming

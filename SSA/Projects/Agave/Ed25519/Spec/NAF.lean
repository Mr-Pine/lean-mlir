import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# The carry/window arithmetic of `Scalar::non_adjacent_form`

Pinned source: solana-ed25519 0.2.4, `src/scalar.rs:1025–1076`.
The transition below follows the source's three branches exactly, after
normalizing its five-word shift/mask to the current natural-number tail.
It is a mathematical specification, not an extraction theorem. In particular,
connecting `tail % 2^w` to the two-word LLVM window remains an RIR obligation.
-/
namespace Agave.Ed25519.NAF

/-- The two widths used by the serial and AVX2 double-base loops. -/
def Supported (w : Nat) : Prop := w = 5 ∨ w = 8

structure State where
  tail : Nat
  carry : Nat
  deriving DecidableEq

structure Step where
  digit : Int
  advance : Nat
  next : State

/-- Source carry/window transition; zero digits between nonzero digits are
represented by `advance`, rather than writing into an array. -/
def step (w : Nat) (s : State) : Step :=
  let width := 2 ^ w
  let window := s.carry + s.tail % width
  if window % 2 = 0 then
    ⟨0, 1, ⟨s.tail / 2, s.carry⟩⟩
  else if window < width / 2 then
    ⟨window, w, ⟨s.tail / width, 0⟩⟩
  else
    ⟨(window : Int) - width, w, ⟨s.tail / width, 1⟩⟩

def value (s : State) : Nat := s.tail + s.carry

/-- Each source iteration advances the output position, so 256 iterations
suffice to leave the 256-entry output array. -/
theorem advance_bounds (w : Nat) (hw : Supported w) (s : State) :
    1 ≤ (step w s).advance ∧ (step w s).advance ≤ 8 := by
  rcases hw with rfl | rfl <;> simp only [step] <;> split_ifs <;> norm_num

/-- Both source word loads are in the five-word buffer. -/
theorem word_indices_safe (pos : Nat) (hp : pos < 256) :
    pos / 64 < 5 ∧ 1 + pos / 64 < 5 := by omega

/-- The second-word shift is never by 64; this matters for LLVM poison. -/
theorem cross_word_shift_safe (pos w : Nat) (hw : Supported w)
    (hcross : ¬pos % 64 < 64 - w) :
    0 < 64 - pos % 64 ∧ 64 - pos % 64 < 64 := by
  have := Nat.mod_lt pos (by decide : 0 < 64)
  rcases hw with rfl | rfl <;> omega

/-- Updating the normalized tail agrees with advancing the source cursor. -/
theorem next_tail_eq (w : Nat) (s : State) :
    (step w s).next.tail = s.tail / 2 ^ (step w s).advance := by
  simp only [step]
  split_ifs <;> simp

/-- The source does not mutate its scalar words. Their current tail is the
original scalar shifted by the current position, also after a transition. -/
theorem next_tail_of_original (w n pos carry : Nat) :
    (step w ⟨n / 2 ^ pos, carry⟩).next.tail =
      n / 2 ^ (pos + (step w ⟨n / 2 ^ pos, carry⟩).advance) := by
  rw [next_tail_eq]
  simp only [Nat.div_div_eq_div_mul, pow_add]

/-- Carry remains a single bit. -/
theorem carry_bound (w : Nat) (s : State) (hc : s.carry ≤ 1) :
    (step w s).next.carry ≤ 1 := by
  simp only [step]
  split_ifs <;> simp_all

/-- Nonzero digits are odd, and all digits fit i8 without ever being -128.
Consequently absolute-value lookup indices cannot hit the i8 overflow case. -/
theorem digit_bounds (w : Nat) (hw : Supported w) (s : State)
    (hc : s.carry ≤ 1) :
    -(2 ^ (w - 1) : Int) < (step w s).digit ∧
    (step w s).digit < (2 ^ (w - 1) : Int) ∧
    ((step w s).digit = 0 ∨ (step w s).digit % 2 = 1) := by
  rcases hw with rfl | rfl
  · have hm := Nat.mod_lt s.tail (by decide : 0 < 32)
    norm_num [step]
    split_ifs <;> dsimp only <;> omega
  · have hm := Nat.mod_lt s.tail (by decide : 0 < 256)
    norm_num [step]
    split_ifs <;> dsimp only <;> omega

/-- The mathematical digit agrees with its signed eight-bit representation. -/
theorem digit_i8_roundtrip (w : Nat) (hw : Supported w) (s : State)
    (hc : s.carry ≤ 1) : (BitVec.ofInt 8 (step w s).digit).toInt = (step w s).digit := by
  have hb := digit_bounds w hw s hc
  apply BitVec.toInt_ofInt_eq_self (by decide)
  · rcases hw with rfl | rfl <;> norm_num at hb ⊢ <;> omega
  · rcases hw with rfl | rfl <;> norm_num at hb ⊢ <;> omega

/-- A transition preserves the represented integer, including its carry. -/
theorem step_reconstruct (w : Nat) (hw : Supported w) (s : State)
    (hc : s.carry ≤ 1) :
    (value s : Int) = (step w s).digit +
      (2 : Int) ^ (step w s).advance * (value (step w s).next : Int) := by
  rcases hw with rfl | rfl
  · have hd := Nat.mod_add_div s.tail 32
    have h2 := Nat.mod_add_div s.tail 2
    have hm := Nat.mod_lt s.tail (by decide : 0 < 32)
    have hp : s.tail % 32 % 2 = s.tail % 2 := by omega
    norm_num [step, value]
    split_ifs <;> norm_num <;> omega
  · have hd := Nat.mod_add_div s.tail 256
    have h2 := Nat.mod_add_div s.tail 2
    have hm := Nat.mod_lt s.tail (by decide : 0 < 256)
    have hp : s.tail % 256 % 2 = s.tail % 2 := by omega
    norm_num [step, value]
    split_ifs <;> norm_num <;> omega

/-- Every transition at least halves the residual value. This supplies a
termination and reconstruction bound independent of the input digits. -/
theorem next_le_half (w : Nat) (hw : Supported w) (s : State)
    (hc : s.carry ≤ 1) :
    value (step w s).next ≤ value s / 2 := by
  rcases hw with rfl | rfl
  · have hd := Nat.mod_add_div s.tail 32
    have hm := Nat.mod_lt s.tail (by decide : 0 < 32)
    norm_num [step, value]
    split_ifs <;> dsimp only <;> omega
  · have hd := Nat.mod_add_div s.tail 256
    have hm := Nat.mod_lt s.tail (by decide : 0 < 256)
    norm_num [step, value]
    split_ifs <;> dsimp only <;> omega

/-- Evaluate a bounded sequence of the exact carry/window transitions. -/
def evaluate (w : Nat) : Nat → State → Int
  | 0, _ => 0
  | fuel + 1, s =>
      let t := step w s
      t.digit + 2 ^ t.advance * evaluate w fuel t.next

theorem evaluate_reconstruct (w : Nat) (hw : Supported w)
    (fuel : Nat) (s : State) (hc : s.carry ≤ 1)
    (hb : value s < 2 ^ fuel) : evaluate w fuel s = (value s : Int) := by
  induction fuel generalizing s with
  | zero =>
      have : value s = 0 := by simpa using hb
      simp [evaluate, this]
  | succ fuel ih =>
      have hn := next_le_half w hw s hc
      have hn' : value (step w s).next < 2 ^ fuel := by
        rw [pow_succ] at hb
        omega
      rw [evaluate, ih _ (carry_bound w s hc) hn']
      exact (step_reconstruct w hw s hc).symm

/-- 256 transitions reconstruct every supported scalar. The premise is the
scalar representation invariant, rather than a bound on any intermediate. -/
theorem reconstruct_scalar (w : Nat) (hw : Supported w) (n : Nat)
    (hn : n < 2 ^ 255) : evaluate w 256 ⟨n, 0⟩ = (n : Int) := by
  apply evaluate_reconstruct w hw 256 ⟨n, 0⟩ (by norm_num)
  simp only [value, Nat.add_zero]
  exact lt_trans hn (by norm_num)

/-- The source's output positions and 256-position guard, with a structural
iteration budget. Assigning zero in the even branch agrees with the initial
all-zero output array. -/
def digits (w : Nat) : Nat → Nat → State → Nat → Int
  | 0, _, _, _ => 0
  | fuel + 1, pos, s, i =>
      if pos < 256 then
        let t := step w s
        if i = pos then t.digit else digits w fuel (pos + t.advance) t.next i
      else 0

def sourceDigits (w n : Nat) (i : Fin 256) : Int :=
  digits w 256 0 ⟨n, 0⟩ i.val

theorem digits_bounds (w : Nat) (hw : Supported w) (fuel pos : Nat)
    (s : State) (hc : s.carry ≤ 1) (i : Nat) :
    -(2 ^ (w - 1) : Int) < digits w fuel pos s i ∧
    digits w fuel pos s i < (2 ^ (w - 1) : Int) ∧
    (digits w fuel pos s i = 0 ∨ digits w fuel pos s i % 2 = 1) := by
  have hz : (0 : Int) < 2 ^ (w - 1) := by positivity
  induction fuel generalizing pos s with
  | zero => simp [digits, hz]
  | succ fuel ih =>
      simp only [digits]
      split_ifs with hp hi
      · exact digit_bounds w hw s hc
      · exact ih _ _ (carry_bound w s hc)
      · omega

theorem sourceDigits_bounds (w : Nat) (hw : Supported w) (n : Nat)
    (i : Fin 256) :
    -(2 ^ (w - 1) : Int) < sourceDigits w n i ∧
    sourceDigits w n i < (2 ^ (w - 1) : Int) ∧
    (sourceDigits w n i = 0 ∨ sourceDigits w n i % 2 = 1) :=
  digits_bounds w hw 256 0 ⟨n, 0⟩ (by norm_num) i.val

/-- The signed digit cannot trigger i8 negation overflow. -/
theorem sourceDigits_ne_neg128 (w : Nat) (hw : Supported w)
    (n : Nat) (i : Fin 256) : sourceDigits w n i ≠ -128 := by
  have hb := sourceDigits_bounds w hw n i
  rcases hw with rfl | rfl <;> norm_num at hb <;> omega

/-- Both backend table accesses use `abs(digit)/2`. -/
def lookupIndex (d : Int) : Nat := if d < 0 then (-d).toNat / 2 else d.toNat / 2

theorem sourceDigits_lookup_bound (w : Nat) (hw : Supported w)
    (n : Nat) (i : Fin 256) :
    lookupIndex (sourceDigits w n i) < 2 ^ (w - 2) := by
  have hb := sourceDigits_bounds w hw n i
  rcases hw with rfl | rfl <;> norm_num at hb ⊢ <;>
    simp only [lookupIndex] <;> split_ifs <;> omega

/-- Position reached when the bounded source loop terminates. -/
def finalPosition (w : Nat) : Nat → Nat → State → Nat
  | 0, pos, _ => pos
  | fuel + 1, pos, s =>
      if pos < 256 then
        let t := step w s
        finalPosition w fuel (pos + t.advance) t.next
      else pos

/-- The structural budget never truncates a running source loop. -/
theorem source_loop_terminates (w : Nat) (hw : Supported w)
    (fuel pos : Nat) (s : State) (hb : 256 ≤ pos + fuel) :
    256 ≤ finalPosition w fuel pos s := by
  induction fuel generalizing pos s with
  | zero => simpa [finalPosition] using hb
  | succ fuel ih =>
      simp only [finalPosition]
      split_ifs with hp
      · apply ih
        have ha := (advance_bounds w hw s).1
        omega
      · omega

/-- A nonzero tail cannot survive beyond the scalar's 255-bit limit. -/
theorem position_of_tail_bound (n pos q k : Nat) (hn : n < 2 ^ 255)
    (ht : q * 2 ^ pos ≤ n) (hq : 2 ^ k ≤ q) : pos + k < 255 := by
  by_contra h
  have he : 255 ≤ pos + k := by omega
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) he
  rw [pow_add] at hp
  have hm := Nat.mul_le_mul_left (2 ^ pos) hq
  rw [Nat.mul_comm (2 ^ pos) q] at hm
  omega

/-- Dividing the current tail and advancing by the same number of bits
preserves its upper bound by the original scalar. -/
theorem next_tail_bound (w : Nat) (hw : Supported w) (s : State) (pos : Nat) :
    (step w s).next.tail * 2 ^ (pos + (step w s).advance) ≤ s.tail * 2 ^ pos := by
  have hdiv (k : Nat) : s.tail / 2 ^ k * 2 ^ (pos + k) ≤ s.tail * 2 ^ pos := by
    have h := Nat.mul_le_mul_right (2 ^ pos) (Nat.div_mul_le_self s.tail (2 ^ k))
    simpa [pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  rcases hw with rfl | rfl <;> norm_num [step] <;> split_ifs <;>
    dsimp only <;> first | exact hdiv 1 | exact hdiv 5 | exact hdiv 8

/-- Whenever the next carry is set, its position is at most 255. This rules
out a discarded carry when the source loop exits its fixed output buffer. -/
theorem next_carry_position (w : Nat) (hw : Supported w) (s : State)
    (hc : s.carry ≤ 1) (n pos : Nat) (hn : n < 2 ^ 255)
    (ht : s.tail * 2 ^ pos ≤ n) :
    (step w s).next.carry = 1 → pos + (step w s).advance ≤ 255 := by
  rcases hw with rfl | rfl
  · have hm := Nat.mod_lt s.tail (by decide : 0 < 32)
    norm_num [step]
    split_ifs <;> dsimp only
    · intro hcarry
      have hq : 2 ^ 0 ≤ s.tail := by omega
      have hp := position_of_tail_bound n pos s.tail 0 hn ht hq
      omega
    · norm_num
    · intro _
      have hq : 2 ^ 4 ≤ s.tail := by norm_num; omega
      have hp := position_of_tail_bound n pos s.tail 4 hn ht hq
      omega
  · have hm := Nat.mod_lt s.tail (by decide : 0 < 256)
    norm_num [step]
    split_ifs <;> dsimp only
    · intro hcarry
      have hq : 2 ^ 0 ≤ s.tail := by omega
      have hp := position_of_tail_bound n pos s.tail 0 hn ht hq
      omega
    · norm_num
    · intro _
      have hq : 2 ^ 7 ≤ s.tail := by norm_num; omega
      have hp := position_of_tail_bound n pos s.tail 7 hn ht hq
      omega

/-- Integer represented by the emitted digits, using the source's actual
position guard and advances, including the final partial window. -/
def sourceEvaluate (w : Nat) : Nat → Nat → State → Int
  | 0, _, _ => 0
  | fuel + 1, pos, s =>
      if pos < 256 then
        let t := step w s
        t.digit * 2 ^ pos + sourceEvaluate w fuel (pos + t.advance) t.next
      else 0

theorem terminal_value (n pos : Nat) (s : State) (hn : n < 2 ^ 255)
    (ht : s.tail * 2 ^ pos ≤ n) (hc : s.carry ≤ 1)
    (hp : s.carry = 1 → pos ≤ 255) (hpos : 256 ≤ pos) : value s = 0 := by
  have hq : s.tail = 0 := by
    by_contra h
    have hq : 2 ^ 0 ≤ s.tail := by omega
    have := position_of_tail_bound n pos s.tail 0 hn ht hq
    omega
  unfold value
  omega

/-- Full positional-loop reconstruction. The invariant consists only of a
one-bit carry, the original scalar bound, and its elementary shifted-tail
bound; no digit-correctness hypothesis is assumed. -/
theorem sourceEvaluate_reconstruct (w : Nat) (hw : Supported w)
    (fuel n pos : Nat) (s : State) (hn : n < 2 ^ 255)
    (ht : s.tail * 2 ^ pos ≤ n) (hc : s.carry ≤ 1)
    (hp : s.carry = 1 → pos ≤ 255) (hb : 256 ≤ pos + fuel) :
    sourceEvaluate w fuel pos s = (value s : Int) * 2 ^ pos := by
  induction fuel generalizing pos s with
  | zero =>
      have hv := terminal_value n pos s hn ht hc hp (by omega)
      simp [sourceEvaluate, hv]
  | succ fuel ih =>
      simp only [sourceEvaluate]
      split_ifs with hpos
      · have htn := le_trans (next_tail_bound w hw s pos) ht
        have hcn := carry_bound w s hc
        have hpn := next_carry_position w hw s hc n pos hn ht
        have hbn : 256 ≤ pos + (step w s).advance + fuel := by
          have := (advance_bounds w hw s).1
          omega
        rw [ih _ _ htn hcn hpn hbn, pow_add]
        have hs := step_reconstruct w hw s hc
        rw [hs]
        ring
      · have hv := terminal_value n pos s hn ht hc hp (by omega)
        simp [hv]

theorem source_reconstruct_scalar (w : Nat) (hw : Supported w)
    (n : Nat) (hn : n < 2 ^ 255) : sourceEvaluate w 256 0 ⟨n, 0⟩ = n := by
  simpa [value] using sourceEvaluate_reconstruct w hw 256 n 0 ⟨n, 0⟩ hn
    (by simp) (by norm_num) (by simp) (by norm_num)

/-- All positions below the current cursor retain the initial zero. -/
theorem digits_before (w : Nat) (hw : Supported w) (fuel pos : Nat)
    (s : State) (i : Nat) (hi : i < pos) : digits w fuel pos s i = 0 := by
  induction fuel generalizing pos s with
  | zero => rfl
  | succ fuel ih =>
      simp only [digits]
      split_ifs with hp he
      · omega
      · apply ih
        have := (advance_bounds w hw s).1
        omega
      · rfl

/-- Positional evaluation equals the weighted sum of the actual 256 output
digits. In particular skipped positions contribute zero. -/
theorem sourceEvaluate_eq_digits (w : Nat) (hw : Supported w)
    (fuel pos : Nat) (s : State) :
    sourceEvaluate w fuel pos s =
      ∑ i ∈ Finset.range 256, digits w fuel pos s i * (2 : Int) ^ i := by
  induction fuel generalizing pos s with
  | zero => simp [sourceEvaluate, digits]
  | succ fuel ih =>
      by_cases hp : pos < 256
      · have hnzero : digits w fuel (pos + (step w s).advance) (step w s).next pos = 0 := by
          apply digits_before w hw
          have := (advance_bounds w hw s).1
          omega
        have hsum :
            (∑ i ∈ Finset.range 256, digits w (fuel + 1) pos s i * (2 : Int) ^ i) =
            (step w s).digit * 2 ^ pos +
              ∑ i ∈ Finset.range 256,
                digits w fuel (pos + (step w s).advance) (step w s).next i * (2 : Int) ^ i := by
          calc
            _ = ∑ i ∈ Finset.range 256,
                ((if pos = i then (step w s).digit * (2 : Int) ^ pos else 0) +
                  digits w fuel (pos + (step w s).advance) (step w s).next i * (2 : Int) ^ i) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    by_cases hi : i = pos
                    · subst i; simp [digits, hp, hnzero]
                    · simp [digits, hp, hi, Ne.symm hi]
            _ = _ := by rw [Finset.sum_add_distrib]; simp [hp]
        rw [hsum]
        simp only [sourceEvaluate, hp, ite_true]
        rw [ih]
      · simp [sourceEvaluate, digits, hp]

/-- The sum of the source's 256 signed radix-two digits is the scalar. -/
theorem sourceDigits_reconstruct (w : Nat) (hw : Supported w)
    (n : Nat) (hn : n < 2 ^ 255) :
    (∑ i ∈ Finset.range 256, digits w 256 0 ⟨n, 0⟩ i * (2 : Int) ^ i) = n := by
  rw [← sourceEvaluate_eq_digits w hw]
  exact source_reconstruct_scalar w hw n hn

end Agave.Ed25519.NAF

/-- info: 'Agave.Ed25519.NAF.sourceDigits_reconstruct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.NAF.sourceDigits_reconstruct
/-- info: 'Agave.Ed25519.NAF.sourceDigits_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.NAF.sourceDigits_bounds
/-- info: 'Agave.Ed25519.NAF.sourceDigits_lookup_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.NAF.sourceDigits_lookup_bound
/-- info: 'Agave.Ed25519.NAF.source_loop_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.NAF.source_loop_terminates
/-- info: 'Agave.Ed25519.NAF.digit_i8_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.NAF.digit_i8_roundtrip
